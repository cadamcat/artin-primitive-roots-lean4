import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.ProjectionKernel
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.CubeAdjoint
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.GroupTransfer

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

/-- Averaging a function of one coordinate over a finite product is the coordinate average. -/
theorem pd4c_pi_average_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ι → Type*) [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)]
    (i : ι) (f : X i → ℂ) :
    (Fintype.card ((j : ι) → X j) : ℂ)⁻¹ * ∑ u : (j : ι) → X j, f (u i) =
      (Fintype.card (X i) : ℂ)⁻¹ * ∑ v : X i, f v := by
  let R := (j : {j : ι // j ≠ i}) → X j.1
  let E := Equiv.piSplitAt i X
  have hfirst (v : X i) (r : R) : E.symm (v, r) i = v :=
    congrArg Prod.fst (E.apply_symm_apply (v, r))
  have hcard : Fintype.card ((j : ι) → X j) = Fintype.card (X i) * Fintype.card R := by
    simpa only [Fintype.card_prod] using Fintype.card_congr E
  have hsum : (∑ u : (j : ι) → X j, f (u i)) = (Fintype.card R : ℂ) * ∑ v : X i, f v := by
    rw [← Equiv.sum_comp E.symm (fun u => f (u i)), Fintype.sum_prod_type]
    simp only [hfirst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    rfl
  have hi : (Fintype.card (X i) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hr : (Fintype.card R : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [hsum, hcard, Nat.cast_mul]
  field_simp [hi, hr]

abbrev Pd4cLevelPerm (B : ℕ) := (n : Fin (B + 1)) → Equiv.Perm (Fin n.val)

def pd4c_levelWordEquiv (T : Finset Particle) (B : ℕ) (σ : Pd4cLevelPerm B) :
    Pd4cBoundedWord T B ≃ Pd4cBoundedWord T B := {
  toFun := fun w => ⟨w.1, fun k => w.2 (σ w.1 k)⟩
  invFun := fun w => ⟨w.1, fun k => w.2 ((σ w.1).symm k)⟩
  left_inv := by
    rintro ⟨n, v⟩
    change (⟨n, fun k => v (σ n ((σ n).symm k))⟩ : Pd4cBoundedWord T B) = ⟨n, v⟩
    congr 1
    funext k
    simp
  right_inv := by
    rintro ⟨n, v⟩
    change (⟨n, fun k => v ((σ n).symm (σ n k))⟩ : Pd4cBoundedWord T B) = ⟨n, v⟩
    congr 1
    funext k
    simp
}

def pd4c_levelPermInverse (B : ℕ) : Pd4cLevelPerm B ≃ Pd4cLevelPerm B := {
  toFun := fun σ n => (σ n).symm
  invFun := fun σ n => (σ n).symm
  left_inv := by intro σ; funext n; simp
  right_inv := by intro σ; funext n; simp
}

theorem pd4c_levelWordEquiv_inverse (T : Finset Particle) (B : ℕ) (σ : Pd4cLevelPerm B) :
    pd4c_levelWordEquiv T B (pd4c_levelPermInverse B σ) = (pd4c_levelWordEquiv T B σ).symm := by
  apply Equiv.ext
  rintro ⟨n, v⟩
  rfl

theorem pd4c_word_density_perm_public {T : Finset Particle} {n : ℕ}
    (ν : Particle → ℝ) (w : Fin n → T) (π : Equiv.Perm (Fin n)) :
    pd4c_listDensity ν (pd4c_word (fun k => w (π k))) = pd4c_listDensity ν (pd4c_word w) := by
  have hform (v : Fin n → T) : pd4c_listDensity ν (pd4c_word v) =
      (∏ k : Fin n, ν (v k)) / (n.factorial : ℝ) := by
    simp [pd4c_listDensity, pd4c_word, List.prod_ofFn, Function.comp_def]
  rw [hform, hform]
  exact congrArg (fun a : ℝ => a / (n.factorial : ℝ)) (Equiv.prod_comp π (fun k => ν (w k)))

theorem pd4c_levelWord_density (T : Finset Particle) (B : ℕ) (ν : Particle → ℝ)
    (σ : Pd4cLevelPerm B) (w : Pd4cBoundedWord T B) :
    pd4c_listDensity ν (pd4c_word (pd4c_levelWordEquiv T B σ w).2) =
      pd4c_listDensity ν (pd4c_word w.2) := by
  rcases w with ⟨n, v⟩
  exact pd4c_word_density_perm_public ν v (σ n)

/-- The finite levelwise average is the ordinary list projection at the current word's level. -/
theorem pd4c_levelWord_average (T : Finset Particle) (B : ℕ) (f : List Particle → ℂ)
    (w : Pd4cBoundedWord T B) :
    (Fintype.card (Pd4cLevelPerm B) : ℂ)⁻¹ *
        ∑ σ : Pd4cLevelPerm B, f (pd4c_word (pd4c_levelWordEquiv T B σ w).2) =
      pd4c_listSym f (pd4c_word w.2) := by
  rcases w with ⟨n, v⟩
  rw [pd4c_listSym_word]
  exact pd4c_pi_average_coordinate (fun n : Fin (B + 1) => Equiv.Perm (Fin n.val)) n
    (fun π => f (pd4c_word (fun k => v (π k))))

/-- Projection of a finite-word point mass agrees with projection of its underlying list. -/
theorem pd4c_levelWord_delta (T : Finset Particle) (B : ℕ)
    (v w : Pd4cBoundedWord T B) :
    (Fintype.card (Pd4cLevelPerm B) : ℂ)⁻¹ *
        (∑ σ : Pd4cLevelPerm B, if pd4c_levelWordEquiv T B σ w = v then (1 : ℂ) else 0) =
      pd4c_listDelta (pd4c_word v.2) (pd4c_word w.2) := by
  have hδ (σ : Pd4cLevelPerm B) :
      (if pd4c_levelWordEquiv T B σ w = v then (1 : ℂ) else 0) =
        if pd4c_word (pd4c_levelWordEquiv T B σ w).2 = pd4c_word v.2 then (1 : ℂ) else 0 := by
    by_cases h : pd4c_levelWordEquiv T B σ w = v
    · have hc := congrArg (fun u : Pd4cBoundedWord T B => pd4c_word u.2) h
      simp only [if_pos h, if_pos hc]
    · have hn : pd4c_word (pd4c_levelWordEquiv T B σ w).2 ≠ pd4c_word v.2 :=
        fun heq => h (pd4c_boundedWord_list_injective T B heq)
      simp [h, hn]
  simp only [hδ]
  exact pd4c_levelWord_average T B (fun l => if l = pd4c_word v.2 then (1 : ℂ) else 0) w

/-- Averaged point masses evaluate symmetric continuations in factorial word measure. -/
theorem pd4c_listDelta_word_pairing (T : Finset Particle) (B : ℕ) (ν : Particle → ℝ)
    (v : Pd4cBoundedWord T B) (g : List Particle → ℂ)
    (hg : ∀ l l', l.Perm l' → g l = g l') :
    (∑ w : Pd4cBoundedWord T B, (pd4c_listDensity ν (pd4c_word w.2) : ℂ) *
      pd4c_listDelta (pd4c_word v.2) (pd4c_word w.2) * g (pd4c_word w.2)) =
      (pd4c_listDensity ν (pd4c_word v.2) : ℂ) * g (pd4c_word v.2) := by
  have hpoint (σ : Pd4cLevelPerm B) (w : Pd4cBoundedWord T B) :
      g (pd4c_word (pd4c_levelWordEquiv T B σ w).2) = g (pd4c_word w.2) := by
    rcases w with ⟨n, u⟩
    change g (pd4c_word (fun k => u (σ n k))) = g (pd4c_word u)
    apply hg
    simpa only [pd4c_word, Function.comp_def] using
      Equiv.Perm.ofFn_comp_perm (σ n) (fun k => (u k : Particle))
  have haverage (w : Pd4cBoundedWord T B) :
      (Fintype.card (Pd4cLevelPerm B) : ℂ)⁻¹ *
        ∑ σ : Pd4cLevelPerm B, g (pd4c_word (pd4c_levelWordEquiv T B σ w).2) = g (pd4c_word w.2) := by
    simp only [hpoint, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hd : (Fintype.card (Pd4cLevelPerm B) : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp [hd]
  have hpair := pd4c_finiteAverage_pairing (pd4c_levelWordEquiv T B) (pd4c_levelPermInverse B)
    (pd4c_levelWordEquiv_inverse T B) (fun w => pd4c_listDensity ν (pd4c_word w.2))
    (pd4c_levelWord_density T B ν) (fun w => if w = v then (1 : ℂ) else 0)
    (fun w => g (pd4c_word w.2))
  simp only [pd4c_levelWord_delta, haverage, pd4c_listDelta_star] at hpair
  simpa [mul_ite, ite_mul] using hpair

def pd4c_listPair (T : Finset Particle) (B : ℕ) (ν : Particle → ℝ)
    (F G : List Particle → ℂ) : ℂ :=
  ∑ w : Pd4cBoundedWord T B, (pd4c_listDensity ν (pd4c_word w.2) : ℂ) *
    F (pd4c_word w.2) * G (pd4c_word w.2)

def pd4c_listCreate (p : Particle) (F : List Particle → ℂ) (l : List Particle) : ℂ :=
  F (l ++ [p])

theorem pd4c_listCreate_perm (p : Particle) (F : List Particle → ℂ)
    (hF : ∀ l l', l.Perm l' → F l = F l') :
    ∀ l l', l.Perm l' → pd4c_listCreate p F l = pd4c_listCreate p F l' := by
  intro l l' h
  exact hF _ _ (h.append_right _)

theorem pd4c_listRetrieve_perm (e : Particle) (F : List Particle → ℂ)
    (hF : ∀ l l', l.Perm l' → F l = F l') :
    ∀ l l', l.Perm l' → pd4c_listRetrieve e F l = pd4c_listRetrieve e F l' := by
  intro l l' hl
  obtain ⟨E, hget⟩ := pd4c_finEquiv_of_list_perm hl
  unfold pd4c_listRetrieve
  rw [← Equiv.sum_comp E (fun k : Fin l.length => if l.get k = e then F (removeIndices l {k}) else 0)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← hget k]
  by_cases he : l'.get k = e
  · rw [if_pos he, if_pos he]
    exact hF _ _ (by simpa only [Finset.image_singleton] using
      (pd4c_removeIndices_perm_of_getEquiv E hget {k}).symm)
  · rw [if_neg he, if_neg he]

theorem pd4c_listCreate_cutoff (B : ℕ) (p : Particle) (F : List Particle → ℂ)
    (hF : ∀ l, B < l.length → F l = 0) :
    ∀ l, B < l.length → pd4c_listCreate p F l = 0 := by
  intro l hl
  apply hF
  simpa only [List.length_append, List.length_singleton] using
    lt_of_lt_of_le hl (Nat.le_add_right l.length 1)

theorem pd4c_listPair_comm (T : Finset Particle) (B : ℕ) (ν : Particle → ℝ)
    (F G : List Particle → ℂ) : pd4c_listPair T B ν F G = pd4c_listPair T B ν G F := by
  apply Finset.sum_congr rfl
  intro w hw
  ring

theorem pd4c_listPair_scale (T : Finset Particle) (B : ℕ) (ν : Particle → ℝ)
    (c : ℂ) (F G : List Particle → ℂ) :
    pd4c_listPair T B ν F (fun l => c * G l) = c * pd4c_listPair T B ν F G := by
  unfold pd4c_listPair
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  ring

/-- The generic bounded-word creation identity in actual list-indexed notation. -/
theorem pd4c_list_creation_pairing (T : Finset Particle) (B : ℕ) (ν : Particle → ℝ)
    (e : T) (F G : List Particle → ℂ)
    (hF : ∀ l l', l.Perm l' → F l = F l')
    (hG : ∀ l l', l.Perm l' → G l = G l')
    (hFzero : ∀ l, B < l.length → F l = 0) :
    (ν e : ℂ) * pd4c_listPair T B ν G (pd4c_listCreate e F) =
      pd4c_listPair T B ν F (pd4c_listRetrieve e G) := by
  have h := pd4c_bounded_creation_pairing T B ν e F G hF hG hFzero
  unfold pd4c_listPair pd4c_listRetrieve pd4c_listCreate
  simp only [pd4c_word_retrieve_sum]
  exact h

def pd4c_listTransfer (ν : Particle → ℝ) (V : ℝ) (p q : Particle)
    (stored promoted : Bool) (F : List Particle → ℂ) : List Particle → ℂ :=
  let f := if stored then pd4c_listCreate p F else F
  if promoted then fun l => (V⁻¹ : ℂ) * pd4c_listRetrieve q f l
  else fun l => (ν q : ℂ) * f l

/-- A list-indexed store/promotion transfer has the exact factorial transpose. -/
theorem pd4c_listTransfer_pairing (T : Finset Particle) (B : ℕ) (ν : Particle → ℝ)
    (V : ℝ) (hV : V ≠ 0) (p q : T) (stored promoted : Bool)
    (F G : List Particle → ℂ)
    (hF : ∀ l l', l.Perm l' → F l = F l')
    (hG : ∀ l l', l.Perm l' → G l = G l')
    (hFzero : ∀ l, B < l.length → F l = 0)
    (hGzero : ∀ l, B < l.length → G l = 0) :
    (ν p : ℂ) * (if promoted then (V : ℂ) else 1) *
        pd4c_listPair T B ν G (pd4c_listTransfer ν V p q stored promoted F) =
      (ν q : ℂ) * (if stored then (V : ℂ) else 1) *
        pd4c_listPair T B ν F (pd4c_listTransfer ν V q p promoted stored G) := by
  have hcast : (V : ℂ) ≠ 0 := by exact_mod_cast hV
  cases stored <;> cases promoted
  · simp only [pd4c_listTransfer, Bool.false_eq_true, if_false, mul_one, pd4c_listPair_scale]
    rw [pd4c_listPair_comm T B ν G F]
    ring
  · have h := pd4c_list_creation_pairing T B ν q G F hG hF hGzero
    simp only [pd4c_listTransfer, Bool.false_eq_true, if_false, if_true, mul_one, pd4c_listPair_scale]
    rw [← h]
    field_simp [hcast]
  · have h := pd4c_list_creation_pairing T B ν p F G hF hG hFzero
    simp only [pd4c_listTransfer, Bool.false_eq_true, if_false, if_true, mul_one, pd4c_listPair_scale]
    rw [← h]
    field_simp [hcast]
  · have h₁ := pd4c_list_creation_pairing T B ν q G (pd4c_listCreate p F)
      hG (pd4c_listCreate_perm p F hF) hGzero
    have h₂ := pd4c_list_creation_pairing T B ν p F (pd4c_listCreate q G)
      hF (pd4c_listCreate_perm q G hG) hFzero
    simp only [pd4c_listTransfer, if_true, pd4c_listPair_scale]
    have hpair : (ν p : ℂ) * pd4c_listPair T B ν G
        (pd4c_listRetrieve q (pd4c_listCreate p F)) =
        (ν q : ℂ) * pd4c_listPair T B ν F (pd4c_listRetrieve p (pd4c_listCreate q G)) := by
      rw [← h₁, pd4c_listPair_comm T B ν (pd4c_listCreate p F) (pd4c_listCreate q G)]
      rw [← h₂]
      ring
    calc
      _ = (ν p : ℂ) * pd4c_listPair T B ν G
          (pd4c_listRetrieve q (pd4c_listCreate p F)) := by field_simp [hcast]
      _ = _ := hpair
      _ = _ := by field_simp [hcast]

theorem pd4c_listTransfer_perm (ν : Particle → ℝ) (V : ℝ) (p q : Particle)
    (stored promoted : Bool) (F : List Particle → ℂ)
    (hF : ∀ l l', l.Perm l' → F l = F l') :
    ∀ l l', l.Perm l' → pd4c_listTransfer ν V p q stored promoted F l =
      pd4c_listTransfer ν V p q stored promoted F l' := by
  cases stored <;> cases promoted <;> intro l l' h
  · exact congrArg (fun c : ℂ => (ν q : ℂ) * c) (hF l l' h)
  · exact congrArg (fun c : ℂ => (V⁻¹ : ℂ) * c) (pd4c_listRetrieve_perm q F hF l l' h)
  · exact congrArg (fun c : ℂ => (ν q : ℂ) * c) (pd4c_listCreate_perm p F hF l l' h)
  · exact congrArg (fun c : ℂ => (V⁻¹ : ℂ) * c)
      (pd4c_listRetrieve_perm q (pd4c_listCreate p F) (pd4c_listCreate_perm p F hF) l l' h)

theorem pd4c_bounded_word_representation (T : Finset Particle) (B : ℕ) (l : List Particle)
    (hl : ∀ e ∈ l, e ∈ T) (hB : l.length ≤ B) :
    ∃ w : Pd4cBoundedWord T B, pd4c_word w.2 = l := by
  refine ⟨⟨⟨l.length, by omega⟩, fun k => ⟨l.get k, hl _ (List.get_mem l k)⟩⟩, ?_⟩
  exact List.ofFn_get l

end

end ArtinPrimitiveRoots.TypeII.PD
