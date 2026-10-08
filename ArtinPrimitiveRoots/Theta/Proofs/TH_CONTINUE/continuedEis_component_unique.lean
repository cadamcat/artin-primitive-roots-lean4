import ArtinPrimitiveRoots.Theta.Proofs.TH_CONTINUE.Defs
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

namespace ArtinPrimitiveRoots.A1.Theta

/-- Scalar identity theorem for component expressions, including finite linear combinations:
agreement on the series ball gives agreement on the common continuation domain and equal
residues. This is independent of the particular adelic family.
Guide: `runs/lanes/sol-thin-thglobal/PROOFS.md:797–808`.
Uses frozen `Spec.isOpen_contDomain` and `Spec.isPreconnected_contDomain`.
Consumed by `continuedEis_component_reconstruction`; no continuation-existence input. -/
theorem continuedEis_component_unique (ε ε' : ℝ) (hε : 0 < ε) (hε' : 0 < ε')
    (E E' : ℂ → ℂ) (theta theta' : ℂ)
    (hE : AnalyticOnNhd ℂ E (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) ε))
    (hE' : AnalyticOnNhd ℂ E' (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) ε'))
    (hseries : Set.EqOn E E' (Metric.ball (5 / 2 : ℂ) (1 / 2)))
    (hlaurent : ∃ Ψ : ℂ → ℂ, AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) ε) ∧
      Ψ (1 / 6) = theta ∧ ∀ s ∈ Metric.ball (1 / 6 : ℂ) ε,
        s ≠ 1 / 6 → Ψ s = (s - 1 / 6) * E s)
    (hlaurent' : ∃ Ψ : ℂ → ℂ, AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) ε') ∧
      Ψ (1 / 6) = theta' ∧ ∀ s ∈ Metric.ball (1 / 6 : ℂ) ε',
        s ≠ 1 / 6 → Ψ s = (s - 1 / 6) * E' s) :
    Set.EqOn E E' (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) (min ε ε')) ∧
      theta = theta' := by
  let δ := min ε ε'
  have hδpos : 0 < δ := lt_min hε hε'
  have hδε : δ ≤ ε := min_le_left _ _
  have hδε' : δ ≤ ε' := min_le_right _ _
  have hdom : ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) δ ⊆
      ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) ε := by
    intro s hs
    simp only [ArtinPrimitiveRoots.A1.Spec.contDomain, Set.mem_union] at hs ⊢
    rcases hs with (ha | hb) | hc
    · exact Or.inl (Or.inl ha)
    · exact Or.inl (Or.inr hb)
    · exact Or.inr ⟨Metric.ball_subset_ball hδε hc.1, hc.2⟩
  have hdom' : ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) δ ⊆
      ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) ε' := by
    intro s hs
    simp only [ArtinPrimitiveRoots.A1.Spec.contDomain, Set.mem_union] at hs ⊢
    rcases hs with (ha | hb) | hc
    · exact Or.inl (Or.inl ha)
    · exact Or.inl (Or.inr hb)
    · exact Or.inr ⟨Metric.ball_subset_ball hδε' hc.1, hc.2⟩
  have hball : Metric.ball (5 / 2 : ℂ) (1 / 2) ⊆
      ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) δ := by
    intro s hs
    simp only [ArtinPrimitiveRoots.A1.Spec.contDomain, Set.mem_union]
    exact Or.inl (Or.inr hs)
  have hEδ : AnalyticOnNhd ℂ E (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) δ) :=
    hE.mono hdom
  have hE'δ : AnalyticOnNhd ℂ E' (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) δ) :=
    hE'.mono hdom'
  have hanchor : (5 / 2 : ℂ) ∈ Metric.ball (5 / 2 : ℂ) (1 / 2) := by
    simp
  have hseries_eventually :=
    hseries.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hanchor)
  have hEeq : Set.EqOn E E' (ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) δ) := by
    intro s hs
    exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (𝕜 := ℂ) (f := E) (g := E') hEδ hE'δ
      (ArtinPrimitiveRoots.A1.Spec.isPreconnected_contDomain (1 / 6) δ (by norm_num)
        (by norm_num) hδpos)
      (hball hanchor) hseries_eventually hs
  rcases hlaurent with ⟨Ψ, hΨ, hΨcenter, hΨvalue⟩
  rcases hlaurent' with ⟨Ψ', hΨ', hΨ'center, hΨ'value⟩
  have hΨδ : AnalyticOnNhd ℂ Ψ (Metric.ball (1 / 6 : ℂ) δ) :=
    hΨ.mono (Metric.ball_subset_ball hδε)
  have hΨ'δ : AnalyticOnNhd ℂ Ψ' (Metric.ball (1 / 6 : ℂ) δ) :=
    hΨ'.mono (Metric.ball_subset_ball hδε')
  let c : ℂ := 1 / 6
  let U : Set ℂ := Metric.ball c δ \ {c}
  have hopenU : IsOpen U := Metric.isOpen_ball.sdiff isClosed_singleton
  let a : ℂ := c + (δ / 2 : ℂ)
  have hδhalf : 0 < δ / 2 := by positivity
  have hdist : dist a c = δ / 2 := by
    rw [dist_eq_norm]
    simp [a, c, Complex.norm_real]
    positivity
  have ha_ne : a ≠ c := by
    intro ha
    have hre := congrArg Complex.re ha
    simp [a, c] at hre
    linarith
  have haBall : a ∈ Metric.ball c δ :=
    Metric.mem_ball.2 (by rw [hdist]; linarith)
  have haU : a ∈ U := by
    refine ⟨haBall, ?_⟩
    simpa only [Set.mem_singleton_iff] using ha_ne
  have hUEq : Set.EqOn Ψ Ψ' U := by
    intro s hs
    have hsball : s ∈ Metric.ball c δ := hs.1
    have hsne : s ≠ c := by
      simpa only [Set.mem_singleton_iff] using hs.2
    have hsdom : s ∈ ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) δ := by
      simp only [ArtinPrimitiveRoots.A1.Spec.contDomain, Set.mem_union]
      exact Or.inr ⟨by simpa [c] using hsball, by simpa [c] using hsne⟩
    calc
      Ψ s = (s - (1 / 6 : ℂ)) * E s := hΨvalue s (Metric.ball_subset_ball hδε hsball) hsne
      _ = (s - (1 / 6 : ℂ)) * E' s := by rw [hEeq hsdom]
      _ = Ψ' s := (hΨ'value s (Metric.ball_subset_ball hδε' hsball) hsne).symm
  have hΨeq : Set.EqOn Ψ Ψ' (Metric.ball c δ) := by
    intro s hs
    exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (𝕜 := ℂ) (f := Ψ) (g := Ψ') hΨδ hΨ'δ
      Metric.isPreconnected_ball haBall
      (hUEq.eventuallyEq_of_mem (hopenU.mem_nhds haU)) hs
  constructor
  · exact hEeq
  · calc
      theta = Ψ c := hΨcenter.symm
      _ = Ψ' c := hΨeq (Metric.mem_ball_self hδpos)
      _ = theta' := hΨ'center

end ArtinPrimitiveRoots.A1.Theta
