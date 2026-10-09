import ArtinPrimitiveRoots.Splitting.Proofs.«S7-CONTOUR».Boundary

set_option autoImplicit false

open scoped NumberField Topology
open NumberField IsDedekindDomain Complex Filter

noncomputable section

namespace ArtinPrimitiveRoots.Proofs.s7sol_mellin

open ArtinPrimitiveRoots.Splitting ArtinPrimitiveRoots.Hecke

/-- The zeros of xi are exactly the strict-strip sharp zeta zeros, with positive multiplicities. -/
theorem xi_zero_dictionary (K : Type*) [Field K] [NumberField K] :
    (∀ ρ : ℂ, dedekindXi K ρ = 0 ↔ ρ ∈ nontrivialZeros K) ∧
    (∀ ρ : ℂ, ρ ∈ nontrivialZeros K →
      analyticOrderNatAt (dedekindXi K) ρ = zeroMultiplicity K ρ) ∧
    (∀ ρ : ℂ, ρ ∈ nontrivialZeros K → 0 < zeroMultiplicity K ρ) := by
  have hspec := Classical.choose_spec (dedekind_completed K)
  have hxi : Differentiable ℂ (dedekindXi K) := hspec.1
  have hxi₁ : dedekindXi K 1 ≠ 0 := hspec.2.2.2
  have hFE (s : ℂ) : dedekindXi K (1 - s) = dedekindXi K s := by
    simpa only [dedekindXi] using hspec.2.2.1 s
  have hxiOn : AnalyticOnNhd ℂ (dedekindXi K) Set.univ := fun z _ => hxi.analyticAt z
  have hfinite₁ : analyticOrderAt (dedekindXi K) 1 ≠ ⊤ := by
    rw [(hxi.analyticAt 1).analyticOrderAt_eq_zero.mpr hxi₁]
    simp
  have hfinite (z : ℂ) : analyticOrderAt (dedekindXi K) z ≠ ⊤ :=
    hxiOn.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (Set.mem_univ 1) (Set.mem_univ z) hfinite₁
  have hright {z : ℂ} (hz : 1 ≤ z.re) : dedekindXi K z ≠ 0 := by
    by_cases hz₁ : z = 1
    · simpa [hz₁] using hxi₁
    · have hsharp : dedekindZetaSharp K z ≠ 0 := by
        rcases lt_or_eq_of_le hz with hlt | heq
        · rw [dedekindZetaSharp_eq_core K hlt]
          exact TauCeti.dedekindZeta_ne_zero_of_one_lt_re hlt
        · exact sharp_ne_zero_on_one K heq.symm hz₁
      intro hzero
      apply hsharp
      simp [dedekindZetaSharp, hzero]
  have hleft {z : ℂ} (hz : z.re ≤ 0) : dedekindXi K z ≠ 0 := by
    have hRe : 1 ≤ (1 - z).re := by simp only [sub_re, one_re]; linarith
    rw [← hFE z]
    exact hright hRe
  let U : ℂ → ℂ := fun z => (z * (z - 1))⁻¹ * (dedekindPrefactor K z)⁻¹
  have hfactor : dedekindZetaSharp K = dedekindXi K * U := by
    funext z
    change dedekindXi K z / (z * (z - 1) * dedekindPrefactor K z) =
      dedekindXi K z * ((z * (z - 1))⁻¹ * (dedekindPrefactor K z)⁻¹)
    simp only [div_eq_mul_inv, mul_inv, mul_assoc]
  have hU {z : ℂ} (hpos : 0 < z.re) (hlt : z.re < 1) :
      AnalyticAt ℂ U z ∧ U z ≠ 0 := by
    have hz₀ : z ≠ 0 := by intro hz; rw [hz] at hpos; norm_num at hpos
    have hz₁ : z ≠ 1 := by intro hz; rw [hz] at hlt; norm_num at hlt
    have hpoly : AnalyticAt ℂ (fun w : ℂ => w * (w - 1)) z :=
      analyticAt_id.mul (analyticAt_id.sub analyticAt_const)
    have hpoly₀ : z * (z - 1) ≠ 0 := mul_ne_zero hz₀ (sub_ne_zero.mpr hz₁)
    have hpref₀ := dedekindPrefactor_ne_zero_of_re_pos K hpos
    refine ⟨(hpoly.inv hpoly₀).mul ((differentiable_dedekindPrefactor_inv K).analyticAt z), ?_⟩
    exact mul_ne_zero (inv_ne_zero hpoly₀) (inv_ne_zero hpref₀)
  have hzeros (ρ : ℂ) : dedekindXi K ρ = 0 ↔ ρ ∈ nontrivialZeros K := by
    constructor
    · intro hzero
      have hpos : 0 < ρ.re := by
        by_contra h
        exact hleft (le_of_not_gt h) hzero
      have hlt : ρ.re < 1 := by
        by_contra h
        exact hright (le_of_not_gt h) hzero
      refine ⟨hpos, hlt, ?_⟩
      rw [hfactor]
      change dedekindXi K ρ * U ρ = 0
      rw [hzero, zero_mul]
    · rintro ⟨hpos, hlt, hsharp⟩
      have hu₀ := (hU hpos hlt).2
      rw [hfactor] at hsharp
      change dedekindXi K ρ * U ρ = 0 at hsharp
      exact (mul_eq_zero.mp hsharp).resolve_right hu₀
  have hmult (ρ : ℂ) (hρ : ρ ∈ nontrivialZeros K) :
      analyticOrderNatAt (dedekindXi K) ρ = zeroMultiplicity K ρ := by
    obtain ⟨hu, hu₀⟩ := hU hρ.1 hρ.2.1
    have huord := hu.analyticOrderAt_eq_zero.mpr hu₀
    have horder : analyticOrderAt (dedekindZetaSharp K) ρ =
        analyticOrderAt (dedekindXi K) ρ := by
      rw [hfactor, analyticOrderAt_mul (hxi.analyticAt ρ) hu, huord, add_zero]
    change (analyticOrderAt (dedekindXi K) ρ).toNat =
      (analyticOrderAt (dedekindZetaSharp K) ρ).toNat
    rw [horder]
  refine ⟨hzeros, hmult, ?_⟩
  intro ρ hρ
  rw [← hmult ρ hρ]
  apply Nat.pos_of_ne_zero
  intro hnat
  have horder : analyticOrderAt (dedekindXi K) ρ = 0 := by
    simpa [hnat] using (Nat.cast_analyticOrderNatAt (hfinite ρ)).symm
  exact ((hxi.analyticAt ρ).analyticOrderAt_ne_zero.mpr ((hzeros ρ).mpr hρ)) horder

end ArtinPrimitiveRoots.Proofs.s7sol_mellin
