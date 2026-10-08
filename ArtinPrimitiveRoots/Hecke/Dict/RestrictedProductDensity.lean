import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-! A restricted product is approximated by elements supported at finitely many places. -/

set_option autoImplicit false

open Filter Topology
open Classical
open scoped RestrictedProduct

namespace ArtinPrimitiveRoots.Dictionary

variable {ι : Type*} {G : ι → Type*} {A : ∀ i, Set (G i)}
variable [∀ i, TopologicalSpace (G i)] [∀ i, One (G i)]

/-- Truncating a restricted-product element to successively larger finite sets converges to it. -/
theorem tendsto_restrictedProduct_truncate (hA : ∀ i, (1 : G i) ∈ A i)
    (x : Πʳ i, [G i, A i]) :
    Tendsto (fun s : Finset ι =>
      (⟨fun i => if i ∈ s then x i else 1,
        by
          filter_upwards [show ∀ᶠ i : ι in cofinite, i ∉ s by
            exact (s.finite_toSet.compl_mem_cofinite)] with i hi
          simpa [hi] using hA i⟩ : Πʳ i, [G i, A i])) atTop
      (@nhds (Πʳ i, [G i, A i]) (RestrictedProduct.topologicalSpace G A cofinite) x) := by
  classical
  letI : TopologicalSpace (Πʳ i, [G i, A i]) :=
    RestrictedProduct.topologicalSpace G A cofinite
  let S : Set ι := {i | x i ∈ A i}
  have hS : cofinite ≤ 𝓟 S := le_principal_iff.mpr x.2
  let xS : Πʳ i, [G i, A i]_[𝓟 S] := ⟨x, by
    rw [eventually_principal]
    intro i hi
    simpa [S] using hi⟩
  have hconvPi : Tendsto (fun s : Finset ι => fun i => if i ∈ s then xS i else 1)
      atTop (𝓝 (xS : Π i, G i)) := by
    apply tendsto_pi_nhds.2
    intro i
    have hi : ∀ᶠ s : Finset ι in atTop, i ∈ s := by
      exact eventually_atTop.2 ⟨{i}, fun s hs => Finset.singleton_subset_iff.mp hs⟩
    have heq : (fun s : Finset ι => if i ∈ s then xS i else 1) =ᶠ[atTop]
        fun _ => xS i := by
      filter_upwards [hi] with s hs
      simp [hs]
    exact tendsto_const_nhds.congr' heq.symm
  letI : TopologicalSpace (Πʳ i, [G i, A i]_[𝓟 S]) :=
    RestrictedProduct.topologicalSpace G A (𝓟 S)
  have hconvS : Tendsto (fun s : Finset ι =>
      (⟨fun i => if i ∈ s then xS i else 1,
        by
          rw [eventually_principal]
          intro i hi
          by_cases his : i ∈ s
          · simp [his]
            change x i ∈ A i at hi
            simpa [xS] using hi
          · simpa [his] using hA i⟩ : Πʳ i, [G i, A i]_[𝓟 S])) atTop
      (@nhds (Πʳ i, [G i, A i]_[𝓟 S]) (RestrictedProduct.topologicalSpace G A (𝓟 S)) xS) := by
    apply (RestrictedProduct.isEmbedding_coe_of_principal (R := G) (A := A)
      (S := S)).tendsto_nhds_iff.mpr
    change Tendsto (fun s : Finset ι => fun i => if i ∈ s then xS i else 1)
      atTop (𝓝 (xS : Π i, G i))
    exact hconvPi
  have hinc := (RestrictedProduct.continuous_inclusion (R := G) (A := A) hS).continuousAt
    |>.tendsto.comp hconvS
  have hx : RestrictedProduct.inclusion G A hS xS = x := rfl
  have hfun : (fun s : Finset ι =>
      (⟨fun i => if i ∈ s then x i else 1,
        by
          filter_upwards [show ∀ᶠ i : ι in cofinite, i ∉ s by
            exact (s.finite_toSet.compl_mem_cofinite)] with i hi
          simpa [hi] using hA i⟩ : Πʳ i, [G i, A i])) =
      RestrictedProduct.inclusion G A hS ∘ (fun s : Finset ι =>
        (⟨fun i => if i ∈ s then xS i else 1,
          by
            rw [eventually_principal]
            intro i hi
            by_cases his : i ∈ s
            · simp [his]
              change x i ∈ A i at hi
              simpa [xS] using hi
            · simpa [his] using hA i⟩ : Πʳ i, [G i, A i]_[𝓟 S])) := by
    funext s
    apply Subtype.ext
    rfl
  rw [hfun]
  simpa only [hx] using hinc

end ArtinPrimitiveRoots.Dictionary
