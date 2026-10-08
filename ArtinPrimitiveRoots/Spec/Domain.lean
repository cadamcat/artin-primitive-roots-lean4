import ArtinPrimitiveRoots.Spec.Defs

/-! Continuation-domain node C1. -/

set_option autoImplicit false

open NumberField Matrix MeasureTheory
open scoped MatrixGroups ContDiff BoundedContinuousFunction

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.SpecDomcuspP

open Topology Metric

private lemma norm_real_add_I_le (x y : ℝ) :
    ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ≤ |x| + |y| := by
  calc
    ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ≤ ‖(x : ℂ)‖ + ‖(y : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |x| + |y| := by simp [norm_mul]

private lemma real_ball_perturbation {a r x y : ℝ} (hxy : |x| + |y| < r) :
    (a : ℂ) + (x : ℂ) + (y : ℂ) * Complex.I ∈ Metric.ball (a : ℂ) r := by
  rw [Metric.mem_ball, dist_eq_norm]
  have hsub : (a : ℂ) + (x : ℂ) + (y : ℂ) * Complex.I - (a : ℂ) =
      (x : ℂ) + (y : ℂ) * Complex.I := by ring
  rw [hsub]
  exact (norm_real_add_I_le x y).trans_lt hxy

/-- A punctured disk in the complex plane is preconnected. -/
theorem punctured_ball_preconnected (a r : ℝ) (hr : 0 < r) :
    IsPreconnected (Metric.ball (a : ℂ) r \ {(a : ℂ)}) := by
  let ball : Set ℂ := Metric.ball (a : ℂ) r
  let top : Set ℂ := ball ∩ {z | 0 < z.im}
  let right : Set ℂ := ball ∩ {z | a < z.re}
  let bottom : Set ℂ := ball ∩ {z | z.im < 0}
  let left : Set ℂ := ball ∩ {z | z.re < a}
  have htop : IsPreconnected top := by
    apply ((convex_ball (a : ℂ) r).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hright : IsPreconnected right := by
    apply ((convex_ball (a : ℂ) r).inter (convex_halfSpace_re_gt a)).isPreconnected
  have hbottom : IsPreconnected bottom := by
    apply ((convex_ball (a : ℂ) r).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hleft : IsPreconnected left := by
    apply ((convex_ball (a : ℂ) r).inter (convex_halfSpace_re_lt a)).isPreconnected
  let δ : ℝ := r / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have h2δ : |δ| + |δ| < r := by rw [abs_of_pos hδ]; dsimp [δ]; linarith
  have hpoint (x y : ℝ) (hxy : |x| + |y| < r) :
      (a : ℂ) + (x : ℂ) + (y : ℂ) * Complex.I ∈ ball := by
    exact real_ball_perturbation (a := a) (r := r) (x := x) (y := y) hxy
  let p₁ : ℂ := (a : ℂ) + (δ : ℂ) + (δ : ℂ) * Complex.I
  let p₂ : ℂ := (a : ℂ) + (δ : ℂ) + (-δ : ℂ) * Complex.I
  let p₃ : ℂ := (a : ℂ) + (-δ : ℂ) + (-δ : ℂ) * Complex.I
  have hp₁ball : p₁ ∈ ball := by
    simpa [p₁] using hpoint δ δ h2δ
  have hp₂ball : p₂ ∈ ball := by
    have hraw := hpoint δ (-δ) (by simpa only [abs_neg] using h2δ)
    simpa [p₂] using hraw
  have hp₃ball : p₃ ∈ ball := by
    have hraw := hpoint (-δ) (-δ) (by simpa only [abs_neg] using h2δ)
    simpa [p₃] using hraw
  have hp₁im : 0 < p₁.im := by simpa [p₁, Complex.I] using hδ
  have hp₁re : a < p₁.re := by simp [p₁, Complex.I]; linarith [hδ]
  have hp₂re : a < p₂.re := by simp [p₂, Complex.I]; linarith [hδ]
  have hp₂im : p₂.im < 0 := by simp [p₂, Complex.I]; linarith [hδ]
  have hp₃im : p₃.im < 0 := by simp [p₃, Complex.I]; linarith [hδ]
  have hp₃re : p₃.re < a := by simp [p₃, Complex.I]; linarith [hδ]
  have h₁ : p₁ ∈ top ∩ right := by
    exact ⟨⟨hp₁ball, hp₁im⟩, ⟨hp₁ball, hp₁re⟩⟩
  have h₂ : p₂ ∈ right ∩ bottom := by
    exact ⟨⟨hp₂ball, hp₂re⟩, ⟨hp₂ball, hp₂im⟩⟩
  have h₃ : p₃ ∈ bottom ∩ left := by
    exact ⟨⟨hp₃ball, hp₃im⟩, ⟨hp₃ball, hp₃re⟩⟩
  let first : Set ℂ := top ∪ right
  let second : Set ℂ := first ∪ bottom
  let all : Set ℂ := second ∪ left
  have hu₁ : IsPreconnected first := by
    change IsPreconnected (top ∪ right)
    exact htop.union' ⟨p₁, h₁⟩ hright
  have hp₂first : p₂ ∈ first := by
    change p₂ ∈ top ∪ right
    exact Or.inr h₂.1
  have hu₂ : IsPreconnected second := by
    change IsPreconnected (first ∪ bottom)
    exact hu₁.union' ⟨p₂, hp₂first, h₂.2⟩ hbottom
  have hp₃second : p₃ ∈ second := by
    change p₃ ∈ first ∪ bottom
    exact Or.inr h₃.1
  have hu₃ : IsPreconnected all := by
    change IsPreconnected (second ∪ left)
    exact hu₂.union' ⟨p₃, hp₃second, h₃.2⟩ hleft
  have hcover : Metric.ball (a : ℂ) r \ {(a : ℂ)} = all := by
    ext z
    constructor
    · intro hz
      change z ∈ ball ∧ z ≠ (a : ℂ) at hz
      rcases hz with ⟨hzball, hzne⟩
      by_cases him : 0 < z.im
      · exact Or.inl (Or.inl (Or.inl ⟨hzball, him⟩))
      by_cases him' : z.im < 0
      · exact Or.inl (Or.inr ⟨hzball, him'⟩)
      have him0 : z.im = 0 := by linarith
      by_cases hre : a < z.re
      · exact Or.inl (Or.inl (Or.inr ⟨hzball, hre⟩))
      by_cases hre' : z.re < a
      · exact Or.inr ⟨hzball, hre'⟩
      have hre0 : z.re = a := by linarith
      apply False.elim (hzne ?_)
      apply Complex.ext <;> assumption
    · intro hz
      change z ∈ all at hz
      rcases hz with (((⟨hzball, him⟩ | ⟨hzball, hre⟩) | ⟨hzball, him⟩) | ⟨hzball, hre⟩)
      · refine ⟨?_, ?_⟩
        · exact hzball
        · intro heq
          have heq' : z = (a : ℂ) := Set.mem_singleton_iff.mp heq
          have him0 : z.im = 0 := by simpa using congrArg Complex.im heq'
          change 0 < z.im at him
          linarith
      · refine ⟨hzball, ?_⟩
        intro heq
        have heq' : z = (a : ℂ) := Set.mem_singleton_iff.mp heq
        have hre0 : z.re = a := by simpa using congrArg Complex.re heq'
        change a < z.re at hre
        linarith
      · refine ⟨hzball, ?_⟩
        intro heq
        have heq' : z = (a : ℂ) := Set.mem_singleton_iff.mp heq
        have him0 : z.im = 0 := by simpa using congrArg Complex.im heq'
        change z.im < 0 at him
        linarith
      · refine ⟨hzball, ?_⟩
        intro heq
        have heq' : z = (a : ℂ) := Set.mem_singleton_iff.mp heq
        have hre0 : z.re = a := by simpa using congrArg Complex.re heq'
        change z.re < a at hre
        linarith
  rw [hcover]
  exact hu₃

theorem contDomain_isOpen (s₁ ε : ℝ) :
    IsOpen (ArtinPrimitiveRoots.A1.Spec.contDomain s₁ ε) := by
  have hstrip : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 4 ∧ 0 < z.im ∧ z.im < 1} := by
    have h₁ : IsOpen {z : ℂ | 0 < z.re} := isOpen_Ioi.preimage Complex.continuous_re
    have h₂ : IsOpen {z : ℂ | z.re < 4} := isOpen_Iio.preimage Complex.continuous_re
    have h₃ : IsOpen {z : ℂ | 0 < z.im} := isOpen_Ioi.preimage Complex.continuous_im
    have h₄ : IsOpen {z : ℂ | z.im < 1} := isOpen_Iio.preimage Complex.continuous_im
    simpa only [Set.setOf_and] using h₁.inter (h₂.inter (h₃.inter h₄))
  have hpunctured : IsOpen (Metric.ball (s₁ : ℂ) ε \ {(s₁ : ℂ)}) := by
    rw [Set.diff_eq]
    exact Metric.isOpen_ball.inter isOpen_compl_singleton
  simpa only [ArtinPrimitiveRoots.A1.Spec.contDomain] using
    (hstrip.union Metric.isOpen_ball).union hpunctured

end ArtinPrimitiveRoots.Proofs.SpecDomcuspP

namespace ArtinPrimitiveRoots.A1.Spec

/-- C1 `spec:domain` — P-SPEC.md:248, 427–429. The continuation domain is open and preconnected
for the positive parameters used by P-SPEC. -/
theorem C1_domain (s₁ ε : ℝ) (h₀ : 0 < s₁) (h₁ : s₁ < 4) (hε : 0 < ε) :
    IsOpen (contDomain s₁ ε) ∧ IsPreconnected (contDomain s₁ ε) := by
  constructor
  · exact ArtinPrimitiveRoots.Proofs.SpecDomcuspP.contDomain_isOpen s₁ ε
  · let strip : Set ℂ := {z : ℂ | 0 < z.re ∧ z.re < 4 ∧ 0 < z.im ∧ z.im < 1}
    let conv : Set ℂ := Metric.ball (5 / 2 : ℂ) (1 / 2)
    let punct : Set ℂ := Metric.ball (s₁ : ℂ) ε \ {(s₁ : ℂ)}
    have hstrip : IsPreconnected strip := by
      have hc : Convex ℝ strip := by
        dsimp [strip]
        simpa only [Set.setOf_and] using
          (convex_halfSpace_re_gt 0).inter ((convex_halfSpace_re_lt 4).inter
            ((convex_halfSpace_im_gt 0).inter (convex_halfSpace_im_lt 1)))
      exact hc.isPreconnected
    have hconv : IsPreconnected conv := (convex_ball (5 / 2 : ℂ) (1 / 2)).isPreconnected
    have hpunct : IsPreconnected punct :=
      ArtinPrimitiveRoots.Proofs.SpecDomcuspP.punctured_ball_preconnected s₁ ε hε
    have hcenter : ((5 / 2 : ℂ) + (1 / 4 : ℂ) * Complex.I) ∈ strip ∩ conv := by
      norm_num [strip, conv, Metric.mem_ball, dist_eq_norm, Complex.norm_mul]
    have hbridge : ((strip ∪ conv) ∩ punct).Nonempty := by
      let t : ℝ := min (ε / 2) (1 / 2)
      have ht : 0 < t := lt_min (by linarith) (by norm_num)
      have htε : t < ε := (min_le_left _ _).trans_lt (by linarith)
      have ht1 : t < 1 := (min_le_right _ _).trans_lt (by norm_num)
      let z : ℂ := (s₁ : ℂ) + (t : ℂ) * Complex.I
      have hzstrip : z ∈ strip := by
        simp [strip, z]
        exact ⟨h₀, h₁, ht, ht1⟩
      have hzpunct : z ∈ punct := by
        change dist z (s₁ : ℂ) < ε ∧ z ≠ (s₁ : ℂ)
        constructor
        · rw [dist_eq_norm]
          simpa [z, Complex.norm_mul, abs_of_pos ht] using htε
        · intro hz
          have him : z.im = 0 := by simpa using congrArg Complex.im hz
          simp [z, Complex.I] at him
          linarith
      exact ⟨z, ⟨Or.inl hzstrip, hzpunct⟩⟩
    have hfirst : IsPreconnected (strip ∪ conv) :=
      hstrip.union' ⟨_, hcenter.1, hcenter.2⟩ hconv
    have htotal : IsPreconnected (strip ∪ conv ∪ punct) := hfirst.union' hbridge hpunct
    simpa only [contDomain, strip, conv, punct, Set.union_assoc] using htotal

end ArtinPrimitiveRoots.A1.Spec
