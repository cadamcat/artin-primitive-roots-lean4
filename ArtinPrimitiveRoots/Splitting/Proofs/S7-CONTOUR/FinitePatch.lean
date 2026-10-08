import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

open scoped Topology
open Filter

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

/-- Patch finitely many removable points to obtain a function analytic on a neighborhood. -/
theorem finite_analytic_patch (F : ℂ → ℂ) (S : Finset ℂ) (U : Set ℂ)
    (hreg : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ F z)
    (hrem : ∀ p ∈ S, ∃ R : ℂ → ℂ,
      AnalyticAt ℂ R p ∧ F =ᶠ[𝓝[≠] p] R) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧
      ∀ z : ℂ, z ∉ S → G z = F z := by
  classical
  let R (p : ℂ) (hp : p ∈ S) : ℂ → ℂ := (hrem p hp).choose
  let G : ℂ → ℂ := fun z => if hz : z ∈ S then R z hz z else F z
  have hGoff : ∀ z : ℂ, z ∉ S → G z = F z := by
    intro z hz
    simp only [G, dif_neg hz]
  refine ⟨G, ?_, hGoff⟩
  intro p hpU
  by_cases hp : p ∈ S
  · have han : AnalyticAt ℂ (R p hp) p := (hrem p hp).choose_spec.1
    have hlocal : ∀ᶠ z in 𝓝 p, z ≠ p → F z = R p hp z := by
      have h := (hrem p hp).choose_spec.2
      change ∀ᶠ z in 𝓝[≠] p, F z = R p hp z at h
      exact eventually_nhdsWithin_iff.mp h
    have havoid : ∀ᶠ z in 𝓝 p, z ∉ S.erase p :=
      (S.erase p).isClosed.isOpen_compl.mem_nhds (by simp)
    have hGeq : G =ᶠ[𝓝 p] R p hp := by
      filter_upwards [havoid, hlocal] with z hz hloc
      by_cases hzp : z = p
      · subst z
        simp only [G, dif_pos hp]
      · have hzS : z ∉ S := by
          intro hzS
          exact hz (Finset.mem_erase.mpr ⟨hzp, hzS⟩)
        rw [hGoff z hzS]
        exact hloc hzp
    exact han.congr hGeq.symm
  · have havoid : ∀ᶠ z in 𝓝 p, z ∉ S :=
      S.isClosed.isOpen_compl.mem_nhds hp
    have hGeq : F =ᶠ[𝓝 p] G := by
      filter_upwards [havoid] with z hz
      exact (hGoff z hz).symm
    exact (hreg p hpU hp).congr hGeq

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
