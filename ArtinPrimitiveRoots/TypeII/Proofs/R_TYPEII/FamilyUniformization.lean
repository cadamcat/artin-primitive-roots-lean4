import Mathlib

namespace ArtinPrimitiveRoots.Proofs.r_typeii_p

/-- A pointwise-good family with an eventual bound forces one uniform eventual bound.
The proof is by choosing an increasing sequence of violating points and making one
selection which takes the violating data at those points and the default elsewhere. -/
theorem familyUniformization :
    ∀ (ι : Type) (Good : ℝ → ι → Prop) (R : ℝ → ι → ℝ)
      (default : ℝ → ι) (T : ℝ),
      (∀ x : ℝ, T ≤ x → Good x (default x)) →
      (∀ f : ℝ → ι, (∀ x : ℝ, T ≤ x → Good x (f x)) →
        ∃ C x₀ : ℝ, 0 < C ∧ T ≤ x₀ ∧
          ∀ x : ℝ, x₀ ≤ x → R x (f x) ≤ C) →
      ∃ C x₀ : ℝ, 0 < C ∧ T ≤ x₀ ∧
        ∀ x : ℝ, x₀ ≤ x → ∀ i : ι, Good x i → R x i ≤ C := by
  classical
  intro ι Good R default T hdefault hselection
  by_contra hUniform
  have hbad : ∀ C x₀ : ℝ, 0 < C → T ≤ x₀ →
      ∃ x : ℝ, ∃ i : ι, x₀ ≤ x ∧ Good x i ∧ C < R x i := by
    intro C x₀ hC hTx₀
    by_contra h
    have hgood : ∀ x : ℝ, x₀ ≤ x → ∀ i : ι, Good x i → R x i ≤ C := by
      intro x hx i hi
      by_contra hle
      exact h ⟨x, i, hx, hi, lt_of_not_ge hle⟩
    exact hUniform ⟨C, x₀, hC, hTx₀, hgood⟩
  have hbadPair : ∀ C x₀ : ℝ, 0 < C → T ≤ x₀ →
      ∃ p : ℝ × ι, x₀ ≤ p.1 ∧ Good p.1 p.2 ∧ C < R p.1 p.2 := by
    intro C x₀ hC hTx₀
    obtain ⟨x, i, hx, hi, hR⟩ := hbad C x₀ hC hTx₀
    exact ⟨(x, i), hx, hi, hR⟩
  let p : ℕ → ℝ × ι := Nat.rec
    (Classical.choose (hbadPair 1 (max T 2) (by norm_num) (le_max_left _ _)))
    (fun n prev => Classical.choose
      (hbadPair ((n : ℝ) + 2)
        (max T (max ((n : ℝ) + 3) (prev.1 + 1)))
        (by positivity) (le_max_left _ _)))
  have hp : ∀ n : ℕ,
      (n : ℝ) + 2 ≤ (p n).1 ∧ T ≤ (p n).1 ∧
        Good (p n).1 (p n).2 ∧ (n : ℝ) + 1 < R (p n).1 (p n).2 := by
    intro n
    induction n with
    | zero =>
        rcases Classical.choose_spec
          (hbadPair 1 (max T 2) (by norm_num) (le_max_left _ _))
          with ⟨hmax, hgood, hR⟩
        have hmax' : max T 2 ≤ (p 0).1 := by simpa [p] using hmax
        have hgood' : Good (p 0).1 (p 0).2 := by simpa [p] using hgood
        refine ⟨?_, le_trans (le_max_left T 2) hmax', hgood', ?_⟩
        · have hnum : (2 : ℝ) ≤ (p 0).1 :=
            (le_max_right T (2 : ℝ)).trans hmax'
          simpa using hnum
        · have hR' : 1 < R (p 0).1 (p 0).2 := by simpa [p] using hR
          simpa using hR'
    | succ n ih =>
        have h := Classical.choose_spec
          (hbadPair ((n : ℝ) + 2)
            (max T (max ((n : ℝ) + 3) ((p n).1 + 1)))
            (by positivity) (le_max_left _ _))
        rcases ih with ⟨hidx, hT, -, -⟩
        rcases h with ⟨hx, hgood, hR⟩
        have hx' : max T (max ((n : ℝ) + 3) ((p n).1 + 1)) ≤
            (p (Nat.succ n)).1 := by simpa [p] using hx
        have hgood' : Good (p (Nat.succ n)).1 (p (Nat.succ n)).2 := by
          simpa [p] using hgood
        refine ⟨?_, le_trans (le_max_left _ _) hx', hgood', ?_⟩
        · calc
            (Nat.succ n : ℝ) + 2 = (n : ℝ) + 3 := by simp; ring
            _ ≤ max T (max ((n : ℝ) + 3) ((p n).1 + 1)) :=
              le_trans (le_max_left _ _) (le_max_right _ _)
            _ ≤ (p (Nat.succ n)).1 := hx'
        · have hR' : (n : ℝ) + 2 < R (p (Nat.succ n)).1 (p (Nat.succ n)).2 := by
            simpa [p] using hR
          have hcast : (Nat.succ n : ℝ) + 1 = (n : ℝ) + 2 := by simp; ring
          rw [hcast]
          exact hR'
  have hmonoStep : ∀ n : ℕ, (p n).1 < (p (n + 1)).1 := by
    intro n
    have h := Classical.choose_spec
      (hbadPair ((n : ℝ) + 2)
        (max T (max ((n : ℝ) + 3) ((p n).1 + 1)))
        (by positivity) (le_max_left _ _))
    have hchosen : max T (max ((n : ℝ) + 3) ((p n).1 + 1)) ≤ (p (n + 1)).1 := by
      simpa [p, Nat.add_comm] using h.1
    have hle : (p n).1 + 1 ≤ (p (n + 1)).1 :=
      le_trans
        (le_trans (le_max_right ((n : ℝ) + 3) ((p n).1 + 1))
          (le_max_right T (max ((n : ℝ) + 3) ((p n).1 + 1)))) hchosen
    linarith
  have hmono : StrictMono (fun n : ℕ => (p n).1) := strictMono_nat_of_lt_succ hmonoStep
  let f : ℝ → ι := fun x =>
    if hx : ∃ n : ℕ, (p n).1 = x then (p (Classical.choose hx)).2 else default x
  have hf : ∀ x : ℝ, T ≤ x → Good x (f x) := by
    intro x hx
    by_cases hmem : ∃ n : ℕ, (p n).1 = x
    · let n := Classical.choose hmem
      have hn : (p n).1 = x := Classical.choose_spec hmem
      have hg := (hp n).2.2.1
      simpa [f, hmem, n, hn] using hg
    · simpa [f, hmem] using hdefault x hx
  obtain ⟨C, x₀, hC, hTx₀, hbound⟩ := hselection f hf
  obtain ⟨N, hN⟩ := exists_nat_gt (max C x₀)
  have hCN : C < (N : ℝ) := lt_of_le_of_lt (le_max_left _ _) hN
  have hxN : x₀ ≤ (N : ℝ) + 2 := by
    have hle := le_max_right C x₀
    linarith
  have hx : x₀ ≤ (p N).1 := hxN.trans (hp N).1
  have hupper := hbound (p N).1 hx
  have hlower := (hp N).2.2.2
  have hCscore : C < (N : ℝ) + 1 := by linarith
  have hmem : ∃ n : ℕ, (p n).1 = (p N).1 := ⟨N, rfl⟩
  have hindex : Classical.choose hmem = N := hmono.injective (Classical.choose_spec hmem)
  have hfval : f (p N).1 = (p N).2 := by simp [f, hmem, hindex]
  have hupper' : R (p N).1 (p N).2 ≤ C := by simpa [hfval] using hupper
  exact (not_lt_of_ge hupper') (hCscore.trans hlower)

end ArtinPrimitiveRoots.Proofs.r_typeii_p
