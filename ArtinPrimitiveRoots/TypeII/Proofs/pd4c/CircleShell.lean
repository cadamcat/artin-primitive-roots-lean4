import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.CirclePacking

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- A narrow distance shell contains at most one separated phase of each centered sign. -/
theorem circle_shell_card_le_two {α : Type*} [DecidableEq α]
    (T : Finset α) (φ : α → ℝ) (δ a : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      δ ≤ circleDistance (φ i - φ j)) :
    (T.filter fun i => a < circleDistance (φ i) ∧
      circleDistance (φ i) ≤ a+δ/4).card ≤ 2 := by
  let S := T.filter fun i => a < circleDistance (φ i) ∧ circleDistance (φ i) ≤ a+δ/4
  let center (i : α) := φ i - (round (φ i) : ℤ)
  let P := S.filter fun i => 0 ≤ center i
  let N := S.filter fun i => center i < 0
  have hsepc (i : α) (hi : i ∈ S) (j : α) (hj : j ∈ S) (hne : i ≠ j) :
      δ ≤ |center i - center j| := by
    calc
      _ ≤ circleDistance (φ i - φ j) := hsep i (Finset.mem_filter.mp hi).1
        j (Finset.mem_filter.mp hj).1 hne
      _ ≤ |(φ i - φ j) - ((round (φ i) - round (φ j) : ℤ) : ℝ)| :=
        pd4c_circleDistance_le_abs_sub_int _ _
      _ = _ := by dsimp only [center]; push_cast; congr 1; ring
  have hPrange (i : α) (hi : i ∈ P) : a ≤ center i ∧ center i ≤ a+δ/4 := by
    obtain ⟨hiS, hsign⟩ := Finset.mem_filter.mp hi
    obtain ⟨hlo, hhi⟩ := (Finset.mem_filter.mp hiS).2
    rw [pd4c_circleDistance_eq_round] at hlo hhi
    change a < |center i| at hlo
    change |center i| ≤ a+δ/4 at hhi
    rw [abs_of_nonneg hsign] at hlo hhi
    exact ⟨hlo.le, hhi⟩
  have hNrange (i : α) (hi : i ∈ N) : -(a+δ/4) ≤ center i ∧ center i ≤ -a := by
    obtain ⟨hiS, hsign⟩ := Finset.mem_filter.mp hi
    obtain ⟨hlo, hhi⟩ := (Finset.mem_filter.mp hiS).2
    rw [pd4c_circleDistance_eq_round] at hlo hhi
    change a < |center i| at hlo
    change |center i| ≤ a+δ/4 at hhi
    rw [abs_of_neg hsign] at hlo hhi
    constructor <;> linarith only [hlo, hhi]
  have hP := interval_spacing_card_bound P center a (a+δ/4) δ hδ (by linarith) hPrange
    (fun i hi j hj hne => hsepc i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hne)
  have hN := interval_spacing_card_bound N center (-(a+δ/4)) (-a) δ hδ (by linarith) hNrange
    (fun i hi j hj hne => hsepc i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hne)
  have hcoefP : (a+δ/4-a)/δ+1 = (5/4 : ℝ) := by field_simp [hδ.ne'] <;> ring
  have hcoefN : (-a - -(a+δ/4))/δ+1 = (5/4 : ℝ) := by field_simp [hδ.ne'] <;> ring
  rw [hcoefP] at hP
  rw [hcoefN] at hN
  have hPnat : P.card ≤ 1 := by
    by_contra hn
    have htwo : (2 : ℝ) ≤ P.card := by exact_mod_cast (by omega : 2 ≤ P.card)
    linarith only [hP, htwo]
  have hNnat : N.card ≤ 1 := by
    by_contra hn
    have htwo : (2 : ℝ) ≤ N.card := by exact_mod_cast (by omega : 2 ≤ N.card)
    linarith only [hN, htwo]
  have hdisj : Disjoint P N := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (not_lt_of_ge (Finset.mem_filter.mp hi).2) (Finset.mem_filter.mp hj).2
  have hunion : P ∪ N = S := by
    ext i
    simp only [Finset.mem_union, P, N, Finset.mem_filter]
    constructor
    · rintro (⟨hi, _⟩ | ⟨hi, _⟩) <;> exact hi
    · intro hi
      by_cases hsign : 0 ≤ center i
      · exact Or.inl ⟨hi, hsign⟩
      · exact Or.inr ⟨hi, lt_of_not_ge hsign⟩
  have hc := Finset.card_union_of_disjoint hdisj
  rw [hunion] at hc
  change S.card ≤ 2
  omega

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
