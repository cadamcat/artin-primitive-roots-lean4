import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».Defs
import Mathlib.Data.List.Perm.Basic

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
noncomputable section

private def finsetPermEquiv {α : Type*} [DecidableEq α] (σ : Equiv.Perm α) :
    Finset α ≃ Finset α where
  toFun D := D.image σ.symm
  invFun D := D.image σ
  left_inv D := by
    ext a
    simp
  right_inv D := by
    ext a
    simp

private def finCastEquiv {m n : ℕ} (h : m = n) : Fin m ≃ Fin n where
  toFun i := Fin.cast h i
  invFun i := Fin.cast h.symm i
  left_inv i := by cases h; rfl
  right_inv i := by cases h; rfl

private def listPermFinEquiv {α : Type*} [BEq α] [LawfulBEq α]
    {l₁ l₂ : List α} (h : List.Perm l₁ l₂) : Fin l₂.length ≃ Fin l₁.length where
  toFun := h.symm.idxBij
  invFun := h.idxBij
  left_inv := h.idxBij_leftInverse_idxBij_symm
  right_inv := h.idxBij_symm_leftInverse_idxBij

private theorem filterMap_not {α β : Type*} (xs : List α) (p : α → Prop)
    [DecidablePred p] (f : α → β) :
    xs.filterMap (fun a => if p a then none else some (f a)) =
      (xs.filter fun a => ¬ p a).map f := by
  induction xs with
  | nil => rfl
  | cons a xs ih => by_cases ha : p a <;> simp [ha, ih]

private theorem ofFn_finCastEquiv_finRange {m n : ℕ} (h : m = n) :
    (List.finRange m).map (finCastEquiv h) = List.finRange n := by
  apply List.ext_get (by simp [h])
  intro i hi₁ hi₂
  apply Fin.ext
  simp [finCastEquiv]

private theorem removeIndices_reindex_perm (l : List Particle)
    (σ : Equiv.Perm (Fin l.length)) (D : Finset (Fin l.length)) :
    ∃ D' : Finset (Fin (List.ofFn fun j : Fin l.length => l.get (σ j)).length),
      (∀ j, j ∈ D' ↔ σ (finCastEquiv (by simp) j) ∈ D) ∧
      D'.card = D.card ∧
      List.Perm (removeIndices (List.ofFn fun j : Fin l.length => l.get (σ j)) D')
        (removeIndices l D) := by
  classical
  let l' := List.ofFn fun j : Fin l.length => l.get (σ j)
  have hlen : l'.length = l.length := by simp [l']
  let e : Fin l'.length ≃ Fin l.length := (finCastEquiv hlen).trans σ
  let D' := D.image e.symm
  have hmem (j : Fin l'.length) : j ∈ D' ↔ e j ∈ D := by
    simp only [D', Finset.mem_image]
    constructor
    · rintro ⟨a, ha, haj⟩
      have hEq : a = e j := by
        calc
          a = e (e.symm a) := (e.apply_symm_apply a).symm
          _ = e j := congrArg e haj
      exact hEq ▸ ha
    · intro hj
      exact ⟨e j, hj, e.symm_apply_apply j⟩
  have hcard : D'.card = D.card := by
    exact Finset.card_image_of_injective _ e.symm.injective
  have hindex : List.Perm ((List.finRange l'.length).map e) (List.finRange l.length) := by
    have hcast : (List.finRange l'.length).map (finCastEquiv hlen) = List.finRange l.length :=
      ofFn_finCastEquiv_finRange hlen
    rw [show (List.finRange l'.length).map e =
      ((List.finRange l'.length).map (finCastEquiv hlen)).map σ by
        simp [e, Function.comp_def, List.map_map], hcast]
    exact Equiv.Perm.map_finRange_perm σ
  have hmapFilter (xs : List (Fin l'.length)) :
      (xs.filter (fun j => e j ∉ D)).map e = (xs.map e).filter (fun j => j ∉ D) := by
    induction xs with
    | nil => rfl
    | cons a xs ih =>
        by_cases ha : e a ∈ D <;> simp [ha, ih]
  have hkeep : List.Perm
      (((List.finRange l'.length).filter (fun j => e j ∉ D)).map e)
      ((List.finRange l.length).filter (fun j => j ∉ D)) := by
    rw [hmapFilter _]
    exact hindex.filter _
  refine ⟨D', ?_, hcard, ?_⟩
  · intro j
    simpa [e, D', finCastEquiv, hlen] using hmem j
  · have hget (j : Fin l'.length) : l'.get j = l.get (e j) := by
      have hh := List.get_ofFn (fun k : Fin l.length => l.get (σ k)) j
      change l'.get j = l.get (σ (Fin.cast (by simp) j)) at hh
      rw [hh]
      congr 1
      apply Fin.ext
      simp [e, finCastEquiv]
    change List.Perm
      ((List.finRange l'.length).filterMap
        (fun j => if j ∈ D' then none else some (l'.get j)))
      ((List.finRange l.length).filterMap
        (fun j => if j ∈ D then none else some (l.get j)))
    rw [filterMap_not, filterMap_not]
    have htarget :
        ((List.finRange l'.length).filter (fun j => j ∉ D')).map l'.get =
          ((List.finRange l'.length).filter (fun j => e j ∉ D)).map (l.get ∘ e) := by
      apply List.ext_get (by simp)
      -- This equality is pointwise; list-filter extensionality below is more direct.
      sorry
    rw [htarget]
    have hsource :
        ((List.finRange l.length).filter (fun j => j ∉ D)).map l.get =
          ((List.finRange l.length).filter (fun j => j ∉ D)).map l.get := rfl
    rw [Function.comp_def]
    exact hkeep.map l.get

private theorem hitIndices_reindex (l : List Particle)
    (σ : Equiv.Perm (Fin l.length)) (z : ℤ × ℤ) :
    hitIndices (List.ofFn fun j : Fin l.length => l.get (σ j)) z =
      (hitIndices l z).image ((finCastEquiv (by simp)).trans σ).symm := by
  classical
  let l' := List.ofFn fun j : Fin l.length => l.get (σ j)
  have hlen : l'.length = l.length := by simp [l']
  let e : Fin l'.length ≃ Fin l.length := (finCastEquiv hlen).trans σ
  ext j
  have hget : l'.get j = l.get (e j) := by
    have hh := List.get_ofFn (fun k : Fin l.length => l.get (σ k)) j
    change l'.get j = l.get (σ (Fin.cast (by simp) j)) at hh
    rw [hh]
    congr 1
    apply Fin.ext
    simp [e, finCastEquiv]
  change particleHits (l'.get j) z ↔ j ∈ (hitIndices l z).image e.symm
  rw [hget]
  constructor
  · intro hj
    exact ⟨e j, hj, e.symm_apply_apply j⟩
  · rintro ⟨a, ha, haj⟩
    have hja : a = e j := by
      calc
        a = e (e.symm a) := (e.apply_symm_apply a).symm
        _ = e j := congrArg e haj
    exact hja ▸ ha

private theorem memoryPermute_exists_of_lists_perm {x : ℝ} {K : ℕ}
    (s t : MemPoint x K) (hpos : s.1 = t.1) (hactive : s.2.1 = t.2.1)
    (h : ∀ i : Fin K, List.Perm (s.2.2 i) (t.2.2 i)) :
    ∃ σ : MemoryPermutation s, memoryPermute s σ = t := by
  classical
  have hl : ∀ i : Fin K, (s.2.2 i).length = (t.2.2 i).length := fun i => (h i).length_eq
  let σ : MemoryPermutation s := fun i =>
    (finCastEquiv (hl i)).trans (listPermFinEquiv (h i))
  refine ⟨σ, ?_⟩
  apply Prod.ext
  · exact hpos
  apply Prod.ext
  · exact hactive
  funext i
  change List.ofFn (fun j : Fin (s.2.2 i).length => (s.2.2 i).get (σ i j)) = t.2.2 i
  apply List.ext_get (l₁ := List.ofFn fun j : Fin (s.2.2 i).length =>
    (s.2.2 i).get (σ i j)) (l₂ := t.2.2 i) (hl i)
  intro j hj₁ hj₂
  have hget := (h i).symm.getElem_idxBij_eq_getElem (i := finCastEquiv (hl i) j)
  simpa [σ, listPermFinEquiv] using hget

end
end ArtinPrimitiveRoots.TypeII.PD
