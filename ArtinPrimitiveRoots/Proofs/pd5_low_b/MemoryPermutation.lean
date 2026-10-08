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

def finCastEquiv {m n : ℕ} (h : m = n) : Fin m ≃ Fin n where
  toFun i := Fin.cast h i
  invFun i := Fin.cast h.symm i
  left_inv i := by cases h; rfl
  right_inv i := by cases h; rfl

def finsetImageEquiv {α β : Type*} [DecidableEq α] [DecidableEq β] (e : α ≃ β) :
    Finset α ≃ Finset β where
  toFun s := s.image e
  invFun s := s.image e.symm
  left_inv s := by ext a; simp
  right_inv s := by ext b; simp

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

theorem removeIndices_reindex_perm (l : List Particle)
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
        have ih' := ih
        simp only [decide_not] at ih'
        by_cases ha : e a ∈ D <;> simp [ha, ih']
  have hkeep : List.Perm
      (((List.finRange l'.length).filter (fun j => e j ∉ D)).map e)
      ((List.finRange l.length).filter (fun j => j ∉ D)) := by
    rw [hmapFilter _]
    exact hindex.filter _
  refine ⟨D', ?_, hcard, ?_⟩
  · intro j
    simpa [e, D', finCastEquiv, hlen] using hmem j
  · have hget (j : Fin l'.length) : l'.get j = l.get (e j) := by
      rw [List.get_ofFn]
      congr 1
    change List.Perm
      ((List.finRange l'.length).filterMap
        (fun j => if j ∈ D' then none else some (l'.get j)))
      ((List.finRange l.length).filterMap
        (fun j => if j ∈ D then none else some (l.get j)))
    rw [filterMap_not, filterMap_not]
    have htarget :
        ((List.finRange l'.length).filter (fun j => j ∉ D')).map l'.get =
          ((List.finRange l'.length).filter (fun j => e j ∉ D)).map (l.get ∘ e) := by
      have hfilter :
          (List.finRange l'.length).filter (fun j => j ∉ D') =
            (List.finRange l'.length).filter (fun j => e j ∉ D) := by
        apply List.filter_congr
        intro j hj
        by_cases hjD : j ∈ D'
        · have heD : e j ∈ D := (hmem j).mp hjD
          simp [hjD, heD]
        · have heD : e j ∉ D := fun he => hjD ((hmem j).mpr he)
          simp [hjD, heD]
      rw [hfilter]
      apply List.map_congr_left
      intro j hj
      exact hget j
    rw [htarget]
    simpa only [List.map_map, Function.comp_def] using hkeep.map l.get

theorem hitIndices_reindex (l : List Particle)
    (σ : Equiv.Perm (Fin l.length)) (z : ℤ × ℤ) :
    hitIndices (List.ofFn fun j : Fin l.length => l.get (σ j)) z =
      (hitIndices l z).image ((finCastEquiv (by simp)).trans σ).symm := by
  classical
  let l' := List.ofFn fun j : Fin l.length => l.get (σ j)
  have hlen : l'.length = l.length := by simp [l']
  let e : Fin l'.length ≃ Fin l.length := (finCastEquiv hlen).trans σ
  ext j
  have hget : l'.get j = l.get (e j) := by
      rw [List.get_ofFn]
      congr 1
  simp only [hitIndices, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  change particleHits (l'.get j) z ↔ ∃ a, particleHits (l.get a) z ∧ e.symm a = j
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

theorem hitIndices_perm {l₁ l₂ : List Particle} (h : List.Perm l₁ l₂)
    (z : ℤ × ℤ) :
    hitIndices l₂ z = (hitIndices l₁ z).image h.idxBij := by
  classical
  ext j
  simp only [hitIndices, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hj
    let i := h.symm.idxBij j
    have hget : l₁.get i = l₂.get j := by
      simpa [i] using h.getElem_idxBij_symm_eq_getElem j
    refine ⟨i, hget.symm ▸ hj, ?_⟩
    exact h.idxBij_idxBij_symm
  · rintro ⟨i, hi, hij⟩
    subst j
    have hget : l₂.get (h.idxBij i) = l₁.get i := by
      simpa using h.getElem_idxBij_eq_getElem i
    exact hget ▸ hi

theorem hitCount_perm {l₁ l₂ : List Particle} (h : List.Perm l₁ l₂)
    (z : ℤ × ℤ) : hitCount l₂ z = hitCount l₁ z := by
  change (hitIndices l₂ z).card = (hitIndices l₁ z).card
  rw [hitIndices_perm h z]
  exact Finset.card_image_of_injective _ h.idxBij_injective

theorem listPermute_perm (l : List Particle) (σ : Equiv.Perm (Fin l.length)) :
    List.Perm (List.ofFn fun j : Fin l.length => l.get (σ j)) l := by
  rw [List.ofFn_eq_map]
  have hp : List.Perm (List.map l.get (List.map σ (List.finRange l.length)))
      (List.map l.get (List.finRange l.length)) :=
    (Equiv.Perm.map_finRange_perm σ).map l.get
  have hmap : List.map l.get (List.map σ (List.finRange l.length)) =
      List.map (fun j => l.get (σ j)) (List.finRange l.length) := by
    simp [List.map_map]
  have hlist : List.map l.get (List.finRange l.length) = l := by
    rw [← List.ofFn_eq_map, List.ofFn_get]
  rw [← hmap]
  exact hp.trans (List.Perm.of_eq hlist)

theorem memoryPermute_exists_of_lists_perm {x : ℝ} {K : ℕ}
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
  apply List.ext_get (by simp [hl i])
  intro j hj₁ hj₂
  have hlenOut :
      (List.ofFn fun j : Fin (s.2.2 i).length => (s.2.2 i).get (σ i j)).length =
        (s.2.2 i).length := by simp
  let jOut : Fin ((List.ofFn fun j : Fin (s.2.2 i).length =>
    (s.2.2 i).get (σ i j)).length) := ⟨j, hj₁⟩
  let jSrc : Fin (s.2.2 i).length := Fin.cast hlenOut jOut
  let jT : Fin (t.2.2 i).length := ⟨j, hj₂⟩
  have hget := (h i).symm.getElem_idxBij_eq_getElem (i := jT)
  have hcastST : Fin.cast (hl i) jSrc = jT := by
    apply Fin.ext
    rfl
  have hidx : σ i jSrc = (h i).symm.idxBij jT := by
    change (h i).symm.idxBij (Fin.cast (hl i) jSrc) = (h i).symm.idxBij jT
    exact congrArg (h i).symm.idxBij hcastST
  have hcast : Fin.cast (by simp) jOut = jSrc := by
    apply Fin.ext
    rfl
  change (List.ofFn fun j : Fin (s.2.2 i).length =>
      (s.2.2 i).get (σ i j)).get jOut = (t.2.2 i).get jT
  rw [List.get_ofFn, hcast, hidx]
  simpa using hget

theorem memorySymmetric_eq_of_lists_perm {x : ℝ} {K : ℕ}
    (f : MemPoint x K → ℂ) (hf : IsMemorySymmetric f)
    (s t : MemPoint x K) (hpos : s.1 = t.1) (hactive : s.2.1 = t.2.1)
    (hmem : ∀ i : Fin K, List.Perm (s.2.2 i) (t.2.2 i)) :
    f t = f s := by
  obtain ⟨σ, hσ⟩ := memoryPermute_exists_of_lists_perm s t hpos hactive hmem
  rw [← hσ]
  exact hf s σ

end
end ArtinPrimitiveRoots.TypeII.PD
