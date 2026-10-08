import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

open Set
open scoped Convex

namespace ArtinPrimitiveRoots.A2

/-- An open convex subset of the complex plane stays path connected after removing a
countable set. The intermediate point in the usual two-segment argument is chosen in the
open convex set as well as outside the countably many bad rays. -/
theorem convex_open_diff_countable_isPathConnected {U s : Set ℂ}
    (hconv : Convex ℝ U) (hopen : IsOpen U) (hne : U.Nonempty) (hs : s.Countable) :
    IsPathConnected (U \ s) := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  obtain ⟨a, haS, haU⟩ := (hs.dense_compl ℝ).exists_mem_open hopen hne
  refine ⟨a, ⟨haU, haS⟩, ?_⟩
  intro b hb
  rcases eq_or_ne a b with rfl | hab
  · exact JoinedIn.refl ⟨haU, haS⟩
  let c : ℂ := midpoint ℝ a b
  let x : ℂ := (2 : ℝ)⁻¹ • (b - a)
  have hinvTwo : (⅟ (2 : ℝ)) = (2 : ℝ)⁻¹ := by norm_num
  have Ia : c - x = a := by
    change midpoint ℝ a b - (2 : ℝ)⁻¹ • (b - a) = a
    rw [midpoint_eq_smul_add, hinvTwo]
    module
  have Ib : c + x = b := by
    change midpoint ℝ a b + (2 : ℝ)⁻¹ • (b - a) = b
    rw [midpoint_eq_smul_add, hinvTwo]
    module
  have hx : x ≠ 0 := by
    simpa [x] using sub_ne_zero.2 hab.symm
  have hcU : c ∈ U := hconv.midpoint_mem haU hb.1
  obtain ⟨y, hy⟩ : ∃ y : ℂ, LinearIndependent ℝ ![x, y] :=
    exists_linearIndependent_pair_of_one_lt_rank hrank hx
  have A : {t : ℝ | ([c + x -[ℝ] c + t • y] ∩ s).Nonempty}.Countable := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hs
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have hN : {c + x} ∩ s = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, Ib] using hb.2
    rw [inter_assoc, inter_comm s, inter_assoc, inter_self, ← inter_assoc,
      ← subset_empty_iff, ← hN]
    apply inter_subset_inter_left
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne hy htt'.symm
  have B : {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ s).Nonempty}.Countable := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun t ↦ inter_subset_right) hs
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.2
    have hN : {c - x} ∩ s = ∅ := by
      simpa only [singleton_inter_eq_empty, mem_compl_iff, Ia] using haS
    rw [inter_assoc, inter_comm s, inter_assoc, inter_self, ← inter_assoc,
      ← subset_empty_iff, ← hN]
    apply inter_subset_inter_left
    rw [sub_eq_add_neg _ x]
    apply Eq.subset
    apply segment_inter_eq_endpoint_of_linearIndependent_of_ne _ htt'.symm
    convert hy.units_smul ![-1, 1]
    simp [← List.ofFn_inj]
  let V : Set ℝ := {t | c + t • y ∈ U}
  have hVopen : IsOpen V := by
    exact hopen.preimage (by fun_prop)
  have hVne : V.Nonempty := ⟨0, by simp [V, hcU]⟩
  obtain ⟨t, ht, htV⟩ := (A.union B).dense_compl ℝ |>.exists_mem_open hVopen hVne
  have htA : t ∉ {t : ℝ | ([c + x -[ℝ] c + t • y] ∩ s).Nonempty} := by
    intro htA
    exact ht (Or.inl htA)
  have htB : t ∉ {t : ℝ | ([c - x -[ℝ] c + t • y] ∩ s).Nonempty} := by
    intro htB
    exact ht (Or.inr htB)
  let z : ℂ := c + t • y
  have hzU : z ∈ U := by simpa [V, z] using htV
  have hSegBZ : ([b -[ℝ] z] ∩ s) = ∅ := by
    have h : ¬ ([c + x -[ℝ] c + t • y] ∩ s).Nonempty := htA
    have h' : ([c + x -[ℝ] c + t • y] ∩ s) = ∅ := not_nonempty_iff_eq_empty.mp h
    simpa [Ib, z] using h'
  have hSegAZ : ([a -[ℝ] z] ∩ s) = ∅ := by
    have h : ¬ ([c - x -[ℝ] c + t • y] ∩ s).Nonempty := htB
    have h' : ([c - x -[ℝ] c + t • y] ∩ s) = ∅ := not_nonempty_iff_eq_empty.mp h
    simpa [Ia, z] using h'
  have JA : JoinedIn (U \ s) a z := by
    apply JoinedIn.of_segment_subset
    intro w hw
    refine ⟨hconv.segment_subset haU hzU hw, ?_⟩
    intro hws
    have hmem : w ∈ [a -[ℝ] z] ∩ s := ⟨hw, hws⟩
    rw [hSegAZ] at hmem
    exact hmem
  have JB : JoinedIn (U \ s) b z := by
    apply JoinedIn.of_segment_subset
    intro w hw
    refine ⟨hconv.segment_subset hb.1 hzU hw, ?_⟩
    intro hws
    have hmem : w ∈ [b -[ℝ] z] ∩ s := ⟨hw, hws⟩
    rw [hSegBZ] at hmem
    exact hmem
  exact JA.trans JB.symm

end ArtinPrimitiveRoots.A2
