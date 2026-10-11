import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P0
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».M1
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».Defs
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».S0
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-POISSON».P2.CaseB

/-!
# A2-QS-POISSON, part P2: unweighted ideal Poisson with the residue functional at zero

Uses the completed Dedekind zeta of
AINTLIB (`DedekindResidue.completedDedekindZetaEntire`, functional equation
`Hecke.dedekind_completed`, order bound `Hecke.dedekind_order_one`), `qs_transform_mellin_P0`,
`qs_transform_bounds_P0`, `qs_tail_bound_M1`.

Residue bookkeeping.  `Mellin(f)(s) Y^s ζ_K(s)` has a simple pole at `s = 1` (residue
`ρ_K Y Mellin(f)(1)`) and an at most simple pole at `s = 0`: for `f = h(y²)` the Mellin pole is
simple and `ζ_K` is regular; for `f = (T h)(y²)` the gamma quotient at `s/2` has a pole of
order `r₂` and `ζ_K` a zero of order `r₂ - 1`.  So the residue at `0` is `R_K(f)` (no `log Y`).
-/

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]

/-- P2 (OPUS): unweighted ideal Poisson with explicit residue functional at zero, for the
square-variable weights `h(y²)` and `(T h)(y²)`:
`Σ'_{b ≠ 0} f(N b / Y) = ρ_K Y Mellin(f)(1) + R_K(f) + Y Σ'_{b ≠ 0} (T f)(Y N b)`,
both series absolutely summable. -/
theorem qs_unweighted_poisson_residue_P2 [IsTotallyComplex K]
    (f : ℝ → ℂ) (hf : IsQSSquareWeight K f) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} => ‖f ((Ideal.absNorm b.1 : ℝ) / Y)‖) ∧
      Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        ‖qsTransform K f (Y * (Ideal.absNorm b.1 : ℝ))‖) ∧
      ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, f ((Ideal.absNorm b.1 : ℝ) / Y) =
        (qsResidueOne K : ℂ) * (Y : ℂ) * mellin f 1 + qsResidueZero K f +
          (Y : ℂ) * ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
            qsTransform K f (Y * (Ideal.absNorm b.1 : ℝ)) := by
  obtain ⟨h, hh, rfl | rfl⟩ := hf
  · exact QSP2.p2_core (QSP2.caseAData hh) Y hY
  · exact QSP2.p2_core (QSP2.caseBData hh) Y hY

private theorem qs_dvd_sup_iff_P2 (t a b : Ideal (𝓞 K)) :
    t ∣ a ⊔ b ↔ t ∣ a ∧ t ∣ b := by
  rw [Ideal.dvd_iff_le]
  constructor
  · intro h
    exact ⟨Ideal.dvd_iff_le.mpr (le_sup_left.trans h),
      Ideal.dvd_iff_le.mpr (le_sup_right.trans h)⟩
  · rintro ⟨ha, hb⟩
    exact sup_le (Ideal.dvd_iff_le.mp ha) (Ideal.dvd_iff_le.mp hb)

open Classical in
private theorem qsMu_coprime_sum_P2 (a n : Ideal (𝓞 K)) (hn : n ≠ ⊥) :
    (∑ e ∈ (qsDivisors n).filter (fun e => e ∣ a), (qsMu e : ℤ)) =
      if IsCoprime a n then 1 else 0 := by
  classical
  have hJ : a ⊔ n ≠ ⊥ := by
    intro h
    exact hn (le_bot_iff.mp (by simpa [h] using (le_sup_right : n ≤ a ⊔ n)))
  letI : Fintype {e : Ideal (𝓞 K) // e ∣ a ⊔ n} :=
    UniqueFactorizationMonoid.fintypeSubtypeDvd (a ⊔ n) hJ
  have hset : (qsDivisors n).filter (fun e => e ∣ a) = qsDivisors (a ⊔ n) := by
    ext e
    constructor
    · intro he
      have heN := (Finset.mem_filter.mp he).1
      have heA := (Finset.mem_filter.mp he).2
      have heDvdN := (Finset.mem_filter.mp heN).2
      apply qs_dvd_mem_qsDivisors e (a ⊔ n) hJ
      exact (qs_dvd_sup_iff_P2 e a n).2 ⟨heA, heDvdN⟩
    · intro he
      have heSup := (Finset.mem_filter.mp he).2
      have heParts := (qs_dvd_sup_iff_P2 e a n).mp heSup
      exact Finset.mem_filter.mpr
        ⟨qs_dvd_mem_qsDivisors e n hn heParts.2, heParts.1⟩
  have hsum : (∑ e ∈ qsDivisors (a ⊔ n), (qsMu e : ℤ)) =
      ∑ e : {e : Ideal (𝓞 K) // e ∣ a ⊔ n}, (qsMu e.1 : ℤ) := by
    apply Finset.sum_bij (fun e he => ⟨e, (Finset.mem_filter.mp he).2⟩)
    · intro e he
      exact Finset.mem_univ _
    · intro e he f hf hEq
      exact congrArg Subtype.val hEq
    · intro e he
      exact ⟨e.1, qs_dvd_mem_qsDivisors e.1 (a ⊔ n) hJ e.2, Subtype.ext rfl⟩
    · intro e he
      rfl
  calc
    _ = ∑ e ∈ qsDivisors (a ⊔ n), (qsMu e : ℤ) := by rw [hset]
    _ = ∑ e : {e : Ideal (𝓞 K) // e ∣ a ⊔ n}, (qsMu e.1 : ℤ) := hsum
    _ = if a ⊔ n = ⊤ then 1 else 0 := qsMu_sum_divisors (a ⊔ n) hJ
    _ = if IsCoprime a n then 1 else 0 := by
      rw [Ideal.isCoprime_iff_sup_eq]
      rfl

private noncomputable def qsMulDivEquiv_P2 (e : Ideal (𝓞 K)) (he : e ≠ ⊥) :
    {b : Ideal (𝓞 K) // b ≠ ⊥} ≃
      {a : {I : Ideal (𝓞 K) // I ≠ ⊥} // e ∣ a.1} where
  toFun b := ⟨⟨e * b.1, mul_ne_zero he b.2⟩, ⟨b.1, rfl⟩⟩
  invFun a := ⟨Classical.choose a.2, by
    intro hb
    apply a.1.2
    rw [Classical.choose_spec a.2, hb]
    simp⟩
  left_inv b := by
    apply Subtype.ext
    change Classical.choose (show e ∣ e * b.1 from ⟨b.1, rfl⟩) = b.1
    apply mul_left_cancel₀ he
    exact (Classical.choose_spec (show e ∣ e * b.1 from ⟨b.1, rfl⟩)).symm
  right_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Classical.choose_spec a.2).symm

private theorem qsN_mul_P2 (a b : Ideal (𝓞 K)) : qsN (a * b) = qsN a * qsN b := by
  simp [qsN, map_mul]

open Classical in
private theorem qs_dvd_tsum_rescale_P2 (e : Ideal (𝓞 K)) (he : e ≠ ⊥)
    (F : ℝ → ℂ) (Z : ℝ) (hZ : 0 < Z) :
    (∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
      if e ∣ b.1 then F (qsN b.1 / Z) else 0) =
    ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, F (qsN b.1 / (Z / qsN e)) := by
  classical
  let divs := {a : {I : Ideal (𝓞 K) // I ≠ ⊥} // e ∣ a.1}
  let f : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℂ := fun a => F (qsN a.1 / Z)
  let s : Set {I : Ideal (𝓞 K) // I ≠ ⊥} := {a | e ∣ a.1}
  have hIndicator :
      (fun a : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        if e ∣ a.1 then f a else 0) = Set.indicator s f := by
    funext a
    by_cases h : e ∣ a.1 <;> simp [s, h]
  have hsubtype :
      (∑' a : {I : Ideal (𝓞 K) // I ≠ ⊥},
        if e ∣ a.1 then f a else 0) =
        ∑' a : divs, F (qsN a.1.1 / Z) := by
    rw [hIndicator, ← tsum_subtype]
    rfl
  have heNpos : 0 < qsN e := by
    have hp := Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
      (mem_nonZeroDivisors_of_ne_zero he)
    exact_mod_cast hp
  calc
    _ = ∑' a : divs, F (qsN a.1.1 / Z) := hsubtype
    _ = ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, F (qsN (e * b.1) / Z) :=
      (Equiv.tsum_eq (qsMulDivEquiv_P2 e he)
        (fun a : divs => F (qsN a.1.1 / Z))).symm
    _ = ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, F (qsN b.1 / (Z / qsN e)) := by
      apply tsum_congr
      intro b
      have hscale : qsN (e * b.1) / Z = qsN b.1 / (Z / qsN e) := by
        rw [qsN_mul_P2]
        field_simp [ne_of_gt hZ, ne_of_gt heNpos]
      rw [hscale]

/-- P2' (IMPL): the coprime square-variable sum split into the five pieces
(Möbius `Σ_{e∣𝔫} μ(e) 1_{e∣b}`, P2 at scale `Z/N e` for `N e ≤ Zhi`, direct sums for
`N e > Zhi`; dual sums with `N e ≤ Ylo` go to the tail). -/
theorem qs_coprime_square_pieces_P2 [IsTotallyComplex K]
    (F : ℝ → ℂ) (hF : IsQSSquareWeight K F) (Z : ℝ) (hZ : 0 < Z) (𝔫 : Ideal (𝓞 K))
    (h𝔫 : 𝔫 ≠ ⊥) (Ylo Zhi : ℝ) (hYZ : Ylo ≤ Zhi) :
    qsCoprimeSq F Z 𝔫 =
      qsInnerMain K F Z 𝔫 Ylo Zhi - qsInnerHighDiv K F Z 𝔫 Ylo Zhi +
        qsInnerRes K F Z 𝔫 Ylo Zhi + qsInnerTrans K F Z 𝔫 Ylo Zhi +
          qsInnerTail K F Z 𝔫 Ylo Zhi := by
  classical
  let divisors := qsDivisors 𝔫
  let small := divisors.filter (fun e => qsN e ≤ Zhi)
  let large := divisors.filter (fun e => Zhi < qsN e)
  have hP2base := qs_unweighted_poisson_residue_P2 F hF Z hZ
  have hcoeff (b : Ideal (𝓞 K)) :
      (∑ e ∈ divisors, if e ∣ b then (qsMu e : ℂ) else 0) =
        if IsCoprime b 𝔫 then 1 else 0 := by
    calc
      _ = ∑ e ∈ (qsDivisors 𝔫).filter (fun e => e ∣ b), (qsMu e : ℂ) := by
        rw [← Finset.sum_filter]
      _ = _ := by
        exact_mod_cast qsMu_coprime_sum_P2 b 𝔫 h𝔫
  have hpoint (b : {I : Ideal (𝓞 K) // I ≠ ⊥}) :
      (if IsCoprime b.1 𝔫 then F (qsN b.1 / Z) else 0) =
        ∑ e ∈ divisors, if e ∣ b.1 then (qsMu e : ℂ) * F (qsN b.1 / Z) else 0 := by
    calc
      _ = (if IsCoprime b.1 𝔫 then (1 : ℂ) else 0) * F (qsN b.1 / Z) := by
        by_cases hc : IsCoprime b.1 𝔫 <;> simp [hc]
      _ = (∑ e ∈ divisors, if e ∣ b.1 then (qsMu e : ℂ) else 0) *
            F (qsN b.1 / Z) := by rw [hcoeff]
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e he
        by_cases hdiv : e ∣ b.1 <;> simp [hdiv]
  have hfilteredSummable (e : Ideal (𝓞 K)) :
      Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        if e ∣ b.1 then F (qsN b.1 / Z) else 0) := by
    apply Summable.of_norm_bounded hP2base.1.norm
    intro b
    by_cases hdiv : e ∣ b.1 <;> simp [hdiv]
  have htermSummable (e : Ideal (𝓞 K)) :
      Summable (fun b : {I : Ideal (𝓞 K) // I ≠ ⊥} =>
        if e ∣ b.1 then (qsMu e : ℂ) * F (qsN b.1 / Z) else 0) := by
    have hs := (hfilteredSummable e).mul_left (qsMu e : ℂ)
    exact hs.congr (by
      intro b
      by_cases hdiv : e ∣ b.1 <;> simp [hdiv])
  have hmobius : qsCoprimeSq F Z 𝔫 =
      ∑ e ∈ divisors, ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
        if e ∣ b.1 then (qsMu e : ℂ) * F (qsN b.1 / Z) else 0 := by
    unfold qsCoprimeSq
    calc
      _ = ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
            ∑ e ∈ divisors,
              if e ∣ b.1 then (qsMu e : ℂ) * F (qsN b.1 / Z) else 0 := by
        apply tsum_congr
        exact hpoint
      _ = _ := by
        rw [Summable.tsum_finsetSum (fun e he => htermSummable e)]
  have hdivisorNonzero (e : Ideal (𝓞 K)) (he : e ∈ divisors) : e ≠ ⊥ := by
    intro he0
    have hedvd := (Finset.mem_filter.mp he).2
    rcases hedvd with ⟨u, hu⟩
    apply h𝔫
    rw [he0] at hu
    simpa using hu
  let mainCoefficient : ℂ :=
    (qsResidueOne K : ℂ) * (Z : ℂ) * mellin F 1
  let reciprocal (e : Ideal (𝓞 K)) : ℂ :=
    (qsMu e : ℂ) / (qsN e : ℂ)
  let mainTerm (e : Ideal (𝓞 K)) : ℂ :=
    (qsResidueOne K : ℂ) * ((Z / qsN e : ℝ) : ℂ) * mellin F 1
  let dualTerm (e : Ideal (𝓞 K)) : ℂ :=
    ((Z / qsN e : ℝ) : ℂ) *
      ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
        qsTransform K F (Z * qsN b.1 / qsN e)
  let smallTerm (e : Ideal (𝓞 K)) : ℂ :=
    (qsMu e : ℂ) * (mainTerm e + qsResidueZero K F + dualTerm e)
  let largeTerm (e : Ideal (𝓞 K)) : ℂ :=
    (qsMu e : ℂ) *
      ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, F (qsN e * qsN b.1 / Z)
  have hsmallTerm (e : Ideal (𝓞 K)) (he : e ∈ divisors)
      (hecut : qsN e ≤ Zhi) :
      (∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
        if e ∣ b.1 then (qsMu e : ℂ) * F (qsN b.1 / Z) else 0) =
        smallTerm e := by
    have he0 := hdivisorNonzero e he
    have heNpos : 0 < qsN e := by
      have hp := Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
        (mem_nonZeroDivisors_of_ne_zero he0)
      exact_mod_cast hp
    have hY : 0 < Z / qsN e := div_pos hZ heNpos
    have hpoisson := qs_unweighted_poisson_residue_P2 F hF (Z / qsN e) hY
    have hdualScale :
        (∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
          qsTransform K F ((Z / qsN e) * qsN b.1)) =
        (∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
          qsTransform K F (Z * qsN b.1 / qsN e)) := by
      apply tsum_congr
      intro b
      congr 1
      field_simp [ne_of_gt heNpos]
    calc
      _ = (qsMu e : ℂ) *
            ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              if e ∣ b.1 then F (qsN b.1 / Z) else 0 := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro b
        by_cases hdvd : e ∣ b.1 <;> simp [hdvd]
      _ = (qsMu e : ℂ) *
            ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              F (qsN b.1 / (Z / qsN e)) := by
        rw [qs_dvd_tsum_rescale_P2 e he0 F Z hZ]
      _ = (qsMu e : ℂ) *
            ((qsResidueOne K : ℂ) * ((Z / qsN e : ℝ) : ℂ) * mellin F 1 +
              qsResidueZero K F +
              ((Z / qsN e : ℝ) : ℂ) *
                ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
                  qsTransform K F ((Z / qsN e) * qsN b.1)) := by
        rw [hpoisson.2.2]
      _ = smallTerm e := by
        dsimp [smallTerm, mainTerm, dualTerm]
        rw [hdualScale]
  have hlargeTerm (e : Ideal (𝓞 K)) (he : e ∈ divisors)
      (hecut : Zhi < qsN e) :
      (∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
        if e ∣ b.1 then (qsMu e : ℂ) * F (qsN b.1 / Z) else 0) =
        largeTerm e := by
    have he0 := hdivisorNonzero e he
    have heNpos : 0 < qsN e := by
      have hp := Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
        (mem_nonZeroDivisors_of_ne_zero he0)
      exact_mod_cast hp
    calc
      _ = (qsMu e : ℂ) *
            ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              if e ∣ b.1 then F (qsN b.1 / Z) else 0 := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro b
        by_cases hdvd : e ∣ b.1 <;> simp [hdvd]
      _ = (qsMu e : ℂ) *
            ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              F (qsN b.1 / (Z / qsN e)) := by
        rw [qs_dvd_tsum_rescale_P2 e he0 F Z hZ]
      _ = largeTerm e := by
        dsimp [largeTerm]
        congr 1
        apply tsum_congr
        intro b
        congr 1
        field_simp [ne_of_gt heNpos]
  have hsplit : qsCoprimeSq F Z 𝔫 =
      (∑ e ∈ small, smallTerm e) + (∑ e ∈ large, largeTerm e) := by
    calc
      _ = ∑ e ∈ divisors, ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
            if e ∣ b.1 then (qsMu e : ℂ) * F (qsN b.1 / Z) else 0 := hmobius
      _ = (∑ e ∈ small, ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              if e ∣ b.1 then (qsMu e : ℂ) * F (qsN b.1 / Z) else 0) +
            (∑ e ∈ large, ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              if e ∣ b.1 then (qsMu e : ℂ) * F (qsN b.1 / Z) else 0) := by
        unfold small large
        simpa [not_le] using
          (Finset.sum_filter_add_sum_filter_not divisors
            (fun e => qsN e ≤ Zhi)
            (fun e => ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              if e ∣ b.1 then (qsMu e : ℂ) * F (qsN b.1 / Z) else 0)).symm
      _ = _ := by
        apply congrArg₂ (fun x y : ℂ => x + y)
        · apply Finset.sum_congr rfl
          intro e he
          exact hsmallTerm e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2
        · apply Finset.sum_congr rfl
          intro e he
          exact hlargeTerm e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2
  have hPhiSplitReal : qsPhiRatio 𝔫 =
      (∑ e ∈ small, (qsMu e : ℝ) / (qsN e : ℝ)) +
        ∑ e ∈ large, (qsMu e : ℝ) / (qsN e : ℝ) := by
    unfold qsPhiRatio
    unfold small large
    simpa [qsN, not_le] using
      (Finset.sum_filter_add_sum_filter_not (qsDivisors 𝔫)
        (fun e => qsN e ≤ Zhi)
        (fun e => (qsMu e : ℝ) / (qsN e : ℝ))).symm
  have hPhiSplit : (qsPhiRatio 𝔫 : ℂ) =
      (∑ e ∈ small, reciprocal e) + ∑ e ∈ large, reciprocal e := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hPhiSplitReal
    simpa [reciprocal, qsN, map_add, map_sum, map_div₀, map_intCast, map_natCast] using h
  have hmainSmall :
      (∑ e ∈ small, (qsMu e : ℂ) * mainTerm e) =
        mainCoefficient * ∑ e ∈ small, reciprocal e := by
    calc
      _ = ∑ e ∈ small, mainCoefficient * reciprocal e := by
        apply Finset.sum_congr rfl
        intro e he
        have hediv := (Finset.mem_filter.mp he).1
        have he0 := hdivisorNonzero e hediv
        have heNpos : 0 < qsN e := by
          have hp := Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
            (mem_nonZeroDivisors_of_ne_zero he0)
          exact_mod_cast hp
        have heNcomplex : (qsN e : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt heNpos)
        have heNormComplex : (Ideal.absNorm e : ℂ) ≠ 0 := by
          have hp := Ideal.absNorm_pos_iff_mem_nonZeroDivisors.mpr
            (mem_nonZeroDivisors_of_ne_zero he0)
          exact_mod_cast (ne_of_gt hp)
        have hcast : ((Z / qsN e : ℝ) : ℂ) = (Z : ℂ) / qsN e := by simp
        dsimp [mainCoefficient, reciprocal, mainTerm]
        rw [hcast]
        field_simp [heNcomplex]
        simp [qsN]
        ring
      _ = _ := by rw [Finset.mul_sum]
  have hresSmall :
      (∑ e ∈ small, (qsMu e : ℂ) * qsResidueZero K F) =
        qsResidueZero K F * ∑ e ∈ small, (qsMu e : ℂ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    ring
  let low := divisors.filter (fun e => qsN e ≤ Ylo)
  let trans := divisors.filter (fun e => Ylo < qsN e ∧ qsN e ≤ Zhi)
  have hlowSet : small.filter (fun e => qsN e ≤ Ylo) = low := by
    ext e
    constructor
    · intro he
      have he' : (e ∈ divisors ∧ qsN e ≤ Zhi) ∧ qsN e ≤ Ylo := by
        simpa only [small, Finset.mem_filter] using he
      rcases he' with ⟨⟨hed, heZ⟩, heY⟩
      exact Finset.mem_filter.mpr ⟨hed, heY⟩
    · intro he
      have he' : e ∈ divisors ∧ qsN e ≤ Ylo := by
        simpa only [low, Finset.mem_filter] using he
      rcases he' with ⟨hed, heY⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hed, heY.trans hYZ⟩, heY⟩
  have htransSet : small.filter (fun e => ¬ qsN e ≤ Ylo) = trans := by
    ext e
    constructor
    · intro he
      have he' : (e ∈ divisors ∧ qsN e ≤ Zhi) ∧ ¬ qsN e ≤ Ylo := by
        simpa only [small, Finset.mem_filter] using he
      rcases he' with ⟨⟨hed, heZ⟩, heY⟩
      exact Finset.mem_filter.mpr ⟨hed, ⟨lt_of_not_ge heY, heZ⟩⟩
    · intro he
      have he' : e ∈ divisors ∧ Ylo < qsN e ∧ qsN e ≤ Zhi := by
        simpa only [trans, Finset.mem_filter] using he
      rcases he' with ⟨hed, ⟨heY, heZ⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hed, heZ⟩, not_le.mpr heY⟩
  have hdualSplit :
      (∑ e ∈ small, (qsMu e : ℂ) * dualTerm e) =
        (∑ e ∈ low, (qsMu e : ℂ) * ((Z / qsN e : ℝ) : ℂ) *
          ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
            qsTransform K F (Z * qsN b.1 / qsN e)) +
        ∑ e ∈ trans, (qsMu e : ℂ) * ((Z / qsN e : ℝ) : ℂ) *
          ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
            qsTransform K F (Z * qsN b.1 / qsN e) := by
    calc
      _ = (∑ e ∈ small.filter (fun e => qsN e ≤ Ylo),
            (qsMu e : ℂ) * dualTerm e) +
          ∑ e ∈ small.filter (fun e => ¬ qsN e ≤ Ylo),
            (qsMu e : ℂ) * dualTerm e :=
        (Finset.sum_filter_add_sum_filter_not small (fun e => qsN e ≤ Ylo)
          (fun e => (qsMu e : ℂ) * dualTerm e)).symm
      _ = _ := by
        rw [hlowSet, htransSet]
        apply congrArg₂ (fun x y : ℂ => x + y)
        · apply Finset.sum_congr rfl
          intro e he
          dsimp [dualTerm]
          ring
        · apply Finset.sum_congr rfl
          intro e he
          dsimp [dualTerm]
          ring
  have hsmallSum :
      (∑ e ∈ small, smallTerm e) =
        mainCoefficient * ∑ e ∈ small, reciprocal e +
          qsResidueZero K F * ∑ e ∈ small, (qsMu e : ℂ) +
          (∑ e ∈ low, (qsMu e : ℂ) * ((Z / qsN e : ℝ) : ℂ) *
            ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              qsTransform K F (Z * qsN b.1 / qsN e)) +
          ∑ e ∈ trans, (qsMu e : ℂ) * ((Z / qsN e : ℝ) : ℂ) *
            ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              qsTransform K F (Z * qsN b.1 / qsN e) := by
    calc
      _ = ∑ e ∈ small,
            ((qsMu e : ℂ) * mainTerm e +
              (qsMu e : ℂ) * qsResidueZero K F +
              (qsMu e : ℂ) * dualTerm e) := by
        apply Finset.sum_congr rfl
        intro e he
        dsimp [smallTerm]
        ring
      _ = (∑ e ∈ small, (qsMu e : ℂ) * mainTerm e) +
            (∑ e ∈ small, (qsMu e : ℂ) * qsResidueZero K F) +
            ∑ e ∈ small, (qsMu e : ℂ) * dualTerm e := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = _ := by
        rw [hmainSmall, hresSmall, hdualSplit] <;> ring
  have hlargeSum :
      (∑ e ∈ large, largeTerm e) =
        ∑ e ∈ large, (qsMu e : ℂ) *
          ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, F (qsN e * qsN b.1 / Z) := by
    apply Finset.sum_congr rfl
    intro e he
    rfl
  calc
    qsCoprimeSq F Z 𝔫 =
        mainCoefficient * ∑ e ∈ small, reciprocal e +
          qsResidueZero K F * ∑ e ∈ small, (qsMu e : ℂ) +
          (∑ e ∈ low, (qsMu e : ℂ) * ((Z / qsN e : ℝ) : ℂ) *
            ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              qsTransform K F (Z * qsN b.1 / qsN e)) +
          ∑ e ∈ trans, (qsMu e : ℂ) * ((Z / qsN e : ℝ) : ℂ) *
            ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥},
              qsTransform K F (Z * qsN b.1 / qsN e) +
          ∑ e ∈ large, (qsMu e : ℂ) *
            ∑' b : {I : Ideal (𝓞 K) // I ≠ ⊥}, F (qsN e * qsN b.1 / Z) := by
      rw [hsplit, hsmallSum, hlargeSum]
    _ = qsInnerMain K F Z 𝔫 Ylo Zhi - qsInnerHighDiv K F Z 𝔫 Ylo Zhi +
          qsInnerRes K F Z 𝔫 Ylo Zhi + qsInnerTrans K F Z 𝔫 Ylo Zhi +
            qsInnerTail K F Z 𝔫 Ylo Zhi := by
      unfold qsInnerMain qsInnerHighDiv qsInnerRes qsInnerTrans qsInnerTail
      rw [hPhiSplit]
      dsimp [mainCoefficient, reciprocal]
      ring

end ArtinPrimitiveRoots.A2
