import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

open scoped Topology BigOperators
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

/-- Subtract finitely many simple principal parts and patch the remaining analytic function. -/
theorem finite_principal_parts_patch (H : ℂ → ℂ) (S : Finset ℂ)
    (c : ℂ → ℂ) (U : Set ℂ)
    (hreg : ∀ z ∈ U, z ∉ S → AnalyticAt ℂ H z)
    (hpart : ∀ p ∈ S, ∃ R : ℂ → ℂ, AnalyticAt ℂ R p ∧
      ∀ᶠ z in 𝓝[≠] p, H z = c p / (z - p) + R z) :
    ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G U ∧
      ∀ z : ℂ, z ∉ S → G z = H z - ∑ p ∈ S, c p / (z - p) := by
  classical
  have hsum (T : Finset ℂ) (z : ℂ) (hz : z ∉ T) :
      AnalyticAt ℂ (fun w : ℂ => ∑ q ∈ T, c q / (w - q)) z := by
    revert hz
    induction T using Finset.induction_on with
    | empty =>
        intro hz
        simpa only [Finset.sum_empty] using
          (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) z)
    | @insert q T hq ih =>
        intro hz
        have hzq : z ≠ q := by
          intro heq
          exact hz (Finset.mem_insert.mpr (Or.inl heq))
        have hzT : z ∉ T := by
          intro hzT
          exact hz (Finset.mem_insert.mpr (Or.inr hzT))
        have hterm : AnalyticAt ℂ (fun w : ℂ => c q / (w - q)) z :=
          (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => c q) z).div
            (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hzq)
        have heq : (fun w : ℂ => ∑ r ∈ insert q T, c r / (w - r)) =
            (fun w : ℂ => c q / (w - q)) +
              (fun w : ℂ => ∑ r ∈ T, c r / (w - r)) := by
          funext w
          exact Finset.sum_insert hq
        rw [heq]
        exact hterm.add (ih hzT)
  refine finite_analytic_patch
    (fun z : ℂ => H z - ∑ p ∈ S, c p / (z - p)) S U ?_ ?_
  · intro z hzU hzS
    exact (hreg z hzU hzS).sub (hsum S z hzS)
  · intro p hp
    obtain ⟨R, hR, hlocal⟩ := hpart p hp
    refine ⟨fun z : ℂ => R z - ∑ q ∈ S.erase p, c q / (z - q),
      hR.sub (hsum (S.erase p) p (by simp)), ?_⟩
    filter_upwards [hlocal] with z hz
    change H z - ∑ q ∈ S, c q / (z - q) =
      R z - ∑ q ∈ S.erase p, c q / (z - q)
    rw [← Finset.sum_erase_add S (fun q => c q / (z - q)) hp, hz]
    ring

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
