import Mathlib.Topology.Algebra.FilterBasis
import Mathlib.Topology.Algebra.OpenSubgroup

/-! Group topologies defined by antitone families of splitting subgroups. -/

set_option autoImplicit false
open Filter Topology
open scoped Pointwise
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.th_cover_sol

/-- An antitone subgroup family stable under shrinking conjugation gives a group topology. -/
theorem exists_subgroupBasisTopology {G : Type*} [Group G]
    (m0 : ℕ) (Kc : ℕ → Subgroup G)
    (hanti : ∀ m n, m0 ≤ m → m ≤ n → Kc n ≤ Kc m)
    (hconj : ∀ g : G, ∀ m : ℕ, m0 ≤ m →
      ∃ n : ℕ, m0 ≤ n ∧ ∀ x ∈ Kc n, g * x * g⁻¹ ∈ Kc m) :
    ∃ t : TopologicalSpace G, @IsTopologicalGroup G t inferInstance ∧
      (∀ m, m0 ≤ m → @IsOpen G t (Kc m : Set G)) ∧
      (∀ U ∈ @nhds G t (1 : G), ∃ m, m0 ≤ m ∧ (Kc m : Set G) ⊆ U) := by
  classical
  let b : GroupFilterBasis G := {
    sets := {U | ∃ m : ℕ, m0 ≤ m ∧ U = (Kc m : Set G)}
    nonempty := ⟨(Kc m0 : Set G), m0, le_rfl, rfl⟩
    inter_sets := by
      rintro U W ⟨m, hm, rfl⟩ ⟨n, hn, rfl⟩
      refine ⟨(Kc (max m n) : Set G), ⟨max m n, hm.trans (le_max_left _ _), rfl⟩, ?_⟩
      intro x hx
      exact ⟨hanti m (max m n) hm (le_max_left _ _) hx,
        hanti n (max m n) hn (le_max_right _ _) hx⟩
    one' := by
      rintro U ⟨m, hm, rfl⟩
      exact (Kc m).one_mem
    mul' := by
      rintro U ⟨m, hm, rfl⟩
      refine ⟨(Kc m : Set G), ⟨m, hm, rfl⟩, ?_⟩
      rintro x ⟨a, ha, c, hc, rfl⟩
      exact (Kc m).mul_mem ha hc
    inv' := by
      rintro U ⟨m, hm, rfl⟩
      refine ⟨(Kc m : Set G), ⟨m, hm, rfl⟩, ?_⟩
      intro x hx
      exact (Kc m).inv_mem hx
    conj' := by
      rintro g U ⟨m, hm, rfl⟩
      obtain ⟨n, hn, hgn⟩ := hconj g m hm
      exact ⟨(Kc n : Set G), ⟨n, hn, rfl⟩, hgn⟩
  }
  letI : TopologicalSpace G := b.topology
  letI : IsTopologicalGroup G := b.isTopologicalGroup
  refine ⟨b.topology, b.isTopologicalGroup, ?_, ?_⟩
  · intro m hm
    have hmB : (Kc m : Set G) ∈ b := ⟨m, hm, rfl⟩
    exact (Kc m).isOpen_of_mem_nhds (b.mem_nhds_one hmB)
  · intro U hU
    obtain ⟨V, hV, hVU⟩ := b.nhds_one_hasBasis.mem_iff.mp hU
    obtain ⟨m, hm, rfl⟩ := hV
    exact ⟨m, hm, hVU⟩

end ArtinPrimitiveRoots.Proofs.th_cover_sol
