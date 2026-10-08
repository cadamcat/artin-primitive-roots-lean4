import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Separation.Basic

set_option autoImplicit false

open Filter Topology

namespace ArtinPrimitiveRoots.A2

private noncomputable def finiteCoordinateApprox {ι : Type*} {G : ι → Type*}
    [∀ i, One (G i)] (x : ∀ i, G i) (s : Finset ι) : ∀ i, G i := by
  classical
  exact fun i => if i ∈ s then x i else 1

theorem finiteSupport_dense_pi {ι : Type*} {G : ι → Type*}
    [∀ i, One (G i)] [∀ i, TopologicalSpace (G i)] :
    Dense {x : ∀ i, G i | {i | x i ≠ 1}.Finite} := by
  classical
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_iff_forall.2
  intro x
  rw [mem_closure_iff_nhds]
  intro U hU
  have happrox : Tendsto (finiteCoordinateApprox x) atTop (𝓝 x) := by
    apply tendsto_pi_nhds.2
    intro i
    have heq :
        (fun s : Finset ι => finiteCoordinateApprox x s i) =ᶠ[atTop]
          fun _ : Finset ι => x i := by
      filter_upwards [eventually_atTop.2 ⟨({i} : Finset ι), fun s
        (hs : ({i} : Finset ι) ≤ s) => by
          have hs' : ({i} : Finset ι) ⊆ s := by simpa using hs
          exact Finset.mem_of_subset (s₁ := {i}) (s₂ := s) (a := i) hs' (by simp)⟩] with s hs
      simp [finiteCoordinateApprox, hs]
    exact tendsto_const_nhds.congr' heq.symm
  have hEventually : ∀ᶠ s : Finset ι in atTop, finiteCoordinateApprox x s ∈ U :=
    happrox hU
  obtain ⟨s, hs⟩ := hEventually.exists
  refine ⟨finiteCoordinateApprox x s, hs, ?_⟩
  apply s.finite_toSet.subset
  intro i hi
  simp only [Set.mem_setOf_eq] at hi
  by_contra his
  have his' : i ∉ s := by simpa using his
  have hEq : finiteCoordinateApprox x s i = 1 := by
    simp [finiteCoordinateApprox, his']
  exact hi hEq

theorem continuous_piMonoidHom_eq_one_of_finiteSupport
    {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Monoid (G i)]
    [∀ i, TopologicalSpace (G i)] [Monoid H] [TopologicalSpace H] [T1Space H]
    (φ : (∀ i, G i) →* H) (hφ : Continuous φ)
    (hfs : ∀ x, {i | x i ≠ 1}.Finite → φ x = 1) :
    ∀ x, φ x = 1 := by
  let fs : Set (∀ i, G i) := {x | {i | x i ≠ 1}.Finite}
  have hclosed : IsClosed {x | φ x = 1} := isClosed_singleton.preimage hφ
  have hsub : fs ⊆ {x | φ x = 1} := fun x hx => hfs x hx
  have hclosure : closure fs = (Set.univ : Set (∀ i, G i)) :=
    (finiteSupport_dense_pi).closure_eq
  have hle : closure fs ⊆ {x | φ x = 1} := closure_minimal hsub hclosed
  intro x
  exact hle (by rw [hclosure]; simp)

theorem piMonoidHom_eq_one_of_support_subset
    {ι : Type*} {G : ι → Type*} {H : Type*} [DecidableEq ι] [∀ i, Group (G i)]
    [CommMonoid H] (φ : (∀ i, G i) →* H)
    (hsingle : ∀ i x, φ (Pi.mulSingle i x) = 1) :
    ∀ (x : ∀ i, G i) (s : Finset ι), {i | x i ≠ 1} ⊆ s → φ x = 1 := by
  classical
  intro x s
  induction s using Finset.induction_on generalizing x with
  | empty =>
      intro hx
      have hxeq : x = 1 := by
        funext i
        by_contra hi
        have : i ∈ (∅ : Finset ι) := hx hi
        simpa using this
      simpa [hxeq]
  | @insert i s his ih =>
      intro hx
      let x' : ∀ j, G j := Function.update x i 1
      have hx' : {j | x' j ≠ 1} ⊆ s := by
        intro j hj
        by_cases hji : j = i
        · subst j
          simp [x'] at hj
        · have hjx : x j ≠ 1 := by simpa [x', hji] using hj
          have hj' := hx hjx
          rcases Finset.mem_insert.mp hj' with h | h
          · exact (hji h).elim
          · exact h
      have hdecomp : x = Pi.mulSingle i (x i) * x' := by
        funext j
        by_cases hji : j = i
        · subst j
          simp [x']
        · simp [Pi.mulSingle, x', hji]
      rw [hdecomp, map_mul, hsingle, ih x' hx']
      simp

end ArtinPrimitiveRoots.A2
