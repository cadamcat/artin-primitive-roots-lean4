import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.CubeAdjoint
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Density

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

theorem pd4c_remove_empty (l : List Particle) : removeIndices l ∅ = l := by
  have hmap : (List.finRange l.length).map l.get = l := by
    simpa only [List.ofFn_eq_map] using List.ofFn_get l
  simpa [pd4c_remove_filter_map] using hmap

theorem pd4c_particle_eq_anchor_iff (e : Particle) (p : ℕ) (z : ℤ × ℤ) :
    e = anchorAt p z ↔ e.1 = p ∧ particleHits e z := by
  constructor
  · intro h
    subst e
    exact ⟨rfl, rfl⟩
  · rintro ⟨hp, hh⟩
    apply Prod.ext hp
    change e.2 = (projLine p z).val
    unfold particleHits at hh
    rw [hp] at hh
    exact hh

def pd4c_groupNewMemory {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {i : Fin K}
    (l : List Particle) (p : Particle) (c : EdgeChoice x a l i) : List Particle :=
  removeIndices l (match c.2 with | Sum.inl k => {k} | Sum.inr _ => ∅) ++
    (if c.1 then [p] else [])

def pd4c_listRetrieve (e : Particle) (F : List Particle → ℂ) (l : List Particle) : ℂ :=
  ∑ k : Fin l.length, if l.get k = e then F (removeIndices l {k}) else 0

/-- Fixing a target prime leaves a fresh fill or an indexed retrieval of its anchored particle. -/
theorem pd4c_group_choice_fixed_target {K : ℕ} (F : PDFix K) (S : PDScale) (i : Fin K)
    (l : List Particle) (p : Particle) (q : primeBand S.x (F.a i)) (z' : ℤ × ℤ)
    (stored promoted : Bool) (f : List Particle → ℂ) :
    (∑ c : EdgeChoice S.x F.a l i,
      if c.1 = stored ∧ c.2.isLeft = promoted ∧ edgeNewLabel c = (q : ℕ) ∧
        (match c.2 with | Sum.inl k => particleHits (l.get k) z' | Sum.inr _ => True)
      then (((match c.2 with
        | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
        | Sum.inr r => memoryNu S.x K F.a F.q_d i r : ℝ) : ℂ)) *
          f (pd4c_groupNewMemory l p c)
      else 0) =
      if promoted then
        (((bandMass S.x (F.a i))⁻¹ : ℝ) : ℂ) *
          pd4c_listRetrieve (anchorAt (q : ℕ) z')
            (fun m => if stored then f (m ++ [p]) else f m) l
      else (memoryNu S.x K F.a F.q_d i q : ℂ) *
        (if stored then f (l ++ [p]) else f l) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fintype.sum_sum_type]
  have hcond (k : Fin l.length) :
      ((l.get k).1 = (q : ℕ) ∧ particleHits (l.get k) z') ↔ l.get k = anchorAt (q : ℕ) z' :=
    (pd4c_particle_eq_anchor_iff _ _ _).symm
  have hcond' (k : Fin l.length) :
      (l[k.val].1 = (q : ℕ) ∧ particleHits l[k.val] z') ↔ l[k.val] = anchorAt (q : ℕ) z' := by
    simpa only [List.get_eq_getElem] using hcond k
  cases stored <;> cases promoted
  all_goals simp [pd4c_groupNewMemory, edgeNewLabel, pd4c_remove_empty, hcond',
    pd4c_listRetrieve, mul_ite, Finset.mul_sum, Subtype.coe_inj]

theorem pd4c_edgeNewMemory_component {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (i : Fin K) :
    edgeNewMemory F S s c i = pd4c_groupNewMemory (s.2.2 i)
      (anchorAt (s.2.1 i (lastSlot S.x)) s.1) (c i) := by
  unfold edgeNewMemory pd4c_groupNewMemory
  cases hc : (c i).2 <;> cases hb : (c i).1 <;> simp [hc, hb]

/-- A fixed physical label pair induces a creation/retrieval transfer in one group. -/
def pd4c_groupTransfer {K : ℕ} (ν : Fin K → Particle → ℝ) (V : Fin K → ℝ)
    (i : Fin K) (p q : Particle) (stored promoted : Bool)
    (F : (Fin K → List Particle) → ℂ) : (Fin K → List Particle) → ℂ :=
  let f := if stored then pd4c_create i p F else F
  if promoted then fun l => ((V i)⁻¹ : ℂ) * pd4c_retrieve i q f l
  else fun l => (ν i q : ℂ) * f l

/-- The one-group factorial adjoint exchanges stores and promotions, retaining the V factors. -/
theorem pd4c_groupTransfer_pairing {K : ℕ} (T : Fin K → Finset Particle) (B : ℕ)
    (ν : Fin K → Particle → ℝ) (V : Fin K → ℝ) (i : Fin K) (p q : T i)
    (stored promoted : Bool) (F G : (Fin K → List Particle) → ℂ)
    (hV : V i ≠ 0)
    (hF : ∀ l l', (∀ j, List.Perm (l j) (l' j)) → F l = F l')
    (hG : ∀ l l', (∀ j, List.Perm (l j) (l' j)) → G l = G l')
    (hFzero : ∀ l, B < (l i).length → F l = 0)
    (hGzero : ∀ l, B < (l i).length → G l = 0) :
    (ν i p : ℂ) * (if promoted then (V i : ℂ) else 1) *
        pd4c_cubePair T B ν G (pd4c_groupTransfer ν V i p q stored promoted F) =
      (ν i q : ℂ) * (if stored then (V i : ℂ) else 1) *
        pd4c_cubePair T B ν F (pd4c_groupTransfer ν V i q p promoted stored G) := by
  have hcast : (V i : ℂ) ≠ 0 := by exact_mod_cast hV
  have hscale (c : ℂ) (f g : (Fin K → List Particle) → ℂ) :
      pd4c_cubePair T B ν f (fun l => c * g l) = c * pd4c_cubePair T B ν f g := by
    unfold pd4c_cubePair
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    ring
  cases stored <;> cases promoted
  · simp only [pd4c_groupTransfer, Bool.false_eq_true, if_false, mul_one, hscale]
    rw [pd4c_cubePair_comm T B ν G F]
    ring
  · have h := pd4c_retrieve_create_pairing T B ν i q F G hF hG hGzero
    simp only [pd4c_groupTransfer, Bool.false_eq_true,
      if_false, if_true, mul_one, hscale]
    change pd4c_cubePair T B ν G (pd4c_retrieve i (q : Particle) F) =
      (ν i q : ℂ) * pd4c_cubePair T B ν F (pd4c_create i (q : Particle) G) at h
    rw [h]
    field_simp [hcast]
  · have h := pd4c_create_retrieve_pairing T B ν i p F G hF hG hFzero
    simp only [pd4c_groupTransfer, Bool.false_eq_true,
      if_false, if_true, mul_one, hscale]
    change (ν i p : ℂ) * pd4c_cubePair T B ν G (pd4c_create i (p : Particle) F) =
      pd4c_cubePair T B ν F (pd4c_retrieve i (p : Particle) G) at h
    rw [← h]
    field_simp [hcast]
  · have h := pd4c_store_promote_pairing T B ν i p q F G hF hG hFzero hGzero
    simp only [pd4c_groupTransfer, if_true, hscale]
    calc
      _ = (ν i p : ℂ) * pd4c_cubePair T B ν G
          (pd4c_retrieve i (q : Particle) (pd4c_create i (p : Particle) F)) := by
        field_simp [hcast]
      _ = (ν i q : ℂ) * pd4c_cubePair T B ν F
          (pd4c_retrieve i (p : Particle) (pd4c_create i (q : Particle) G)) := h
      _ = _ := by field_simp [hcast]

end

end ArtinPrimitiveRoots.TypeII.PD
