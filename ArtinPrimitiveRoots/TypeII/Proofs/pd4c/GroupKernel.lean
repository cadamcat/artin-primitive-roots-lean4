import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.ListPairing
import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Damping

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

def pd4c_listDampedDelta (ρ : ℝ) (z : ℤ × ℤ) (m l : List Particle) : ℂ :=
  ((ρ ^ hitCount l z : ℝ) : ℂ) * pd4c_listDelta m l

def pd4c_groupProjectedKernel (ν : Particle → ℝ) (V : ℝ) (p q : Particle)
    (stored promoted : Bool) (ρ : ℝ) (z z' : ℤ × ℤ) (l m : List Particle) : ℂ :=
  ((ρ ^ hitCount l z : ℝ) : ℂ) *
    pd4c_listTransfer ν V p q stored promoted (pd4c_listDampedDelta ρ z' m) l

theorem pd4c_listDampedDelta_perm (ρ : ℝ) (z : ℤ × ℤ) (m : List Particle) :
    ∀ l l', l.Perm l' → pd4c_listDampedDelta ρ z m l = pd4c_listDampedDelta ρ z m l' := by
  intro l l' h
  unfold pd4c_listDampedDelta
  rw [pd4c_hitCount_perm h, pd4c_listDelta_perm m h]

theorem pd4c_listDampedDelta_cutoff (ρ : ℝ) (z : ℤ × ℤ) (m : List Particle)
    (B : ℕ) (hB : m.length ≤ B) : ∀ l, B < l.length → pd4c_listDampedDelta ρ z m l = 0 := by
  intro l hl
  have hne : l.length ≠ m.length := by omega
  simp only [pd4c_listDampedDelta, pd4c_listDelta_zero_of_length_ne m l hne, mul_zero]

theorem pd4c_groupProjectedKernel_perm (ν : Particle → ℝ) (V : ℝ) (p q : Particle)
    (stored promoted : Bool) (ρ : ℝ) (z z' : ℤ × ℤ) (m : List Particle) :
    ∀ l l', l.Perm l' → pd4c_groupProjectedKernel ν V p q stored promoted ρ z z' l m =
      pd4c_groupProjectedKernel ν V p q stored promoted ρ z z' l' m := by
  intro l l' h
  unfold pd4c_groupProjectedKernel
  rw [pd4c_hitCount_perm h]
  rw [pd4c_listTransfer_perm ν V p q stored promoted (pd4c_listDampedDelta ρ z' m)
    (pd4c_listDampedDelta_perm ρ z' m) l l' h]

/-- The projected group kernel has the exact factorial measure transpose, with endpoint damping. -/
theorem pd4c_groupProjectedKernel_transpose (T : Finset Particle) (B : ℕ)
    (ν : Particle → ℝ) (V : ℝ) (hV : V ≠ 0) (p q : T)
    (stored promoted : Bool) (ρ : ℝ) (z z' : ℤ × ℤ) (l m : List Particle)
    (hl : ∀ e ∈ l, e ∈ T) (hm : ∀ e ∈ m, e ∈ T) (hBl : l.length ≤ B) (hBm : m.length ≤ B) :
    (ν p : ℂ) * (if promoted then (V : ℂ) else 1) *
      ((pd4c_listDensity ν l : ℂ) * pd4c_groupProjectedKernel ν V p q stored promoted ρ z z' l m) =
    (ν q : ℂ) * (if stored then (V : ℂ) else 1) *
      ((pd4c_listDensity ν m : ℂ) * pd4c_groupProjectedKernel ν V q p promoted stored ρ z' z m l) := by
  obtain ⟨L, hL⟩ := pd4c_bounded_word_representation T B l hl hBl
  obtain ⟨M, hM⟩ := pd4c_bounded_word_representation T B m hm hBm
  let F := pd4c_listDampedDelta ρ z' m
  let G := pd4c_listDampedDelta ρ z l
  have hpair := pd4c_listTransfer_pairing T B ν V hV p q stored promoted F G
    (pd4c_listDampedDelta_perm ρ z' m) (pd4c_listDampedDelta_perm ρ z l)
    (pd4c_listDampedDelta_cutoff ρ z' m B hBm) (pd4c_listDampedDelta_cutoff ρ z l B hBl)
  have hleft : pd4c_listPair T B ν G (pd4c_listTransfer ν V p q stored promoted F) =
      (pd4c_listDensity ν l : ℂ) * pd4c_groupProjectedKernel ν V p q stored promoted ρ z z' l m := by
    have hev := pd4c_listDelta_word_pairing T B ν L
      (fun u => pd4c_groupProjectedKernel ν V p q stored promoted ρ z z' u m)
      (pd4c_groupProjectedKernel_perm ν V p q stored promoted ρ z z' m)
    rw [hL] at hev
    calc
      _ = ∑ w : Pd4cBoundedWord T B, (pd4c_listDensity ν (pd4c_word w.2) : ℂ) *
          pd4c_listDelta l (pd4c_word w.2) *
            pd4c_groupProjectedKernel ν V p q stored promoted ρ z z' (pd4c_word w.2) m := by
        apply Finset.sum_congr rfl
        intro w hw
        dsimp [G, F, pd4c_listDampedDelta, pd4c_groupProjectedKernel]
        ring
      _ = _ := hev
  have hright : pd4c_listPair T B ν F (pd4c_listTransfer ν V q p promoted stored G) =
      (pd4c_listDensity ν m : ℂ) * pd4c_groupProjectedKernel ν V q p promoted stored ρ z' z m l := by
    have hev := pd4c_listDelta_word_pairing T B ν M
      (fun u => pd4c_groupProjectedKernel ν V q p promoted stored ρ z' z u l)
      (pd4c_groupProjectedKernel_perm ν V q p promoted stored ρ z' z l)
    rw [hM] at hev
    calc
      _ = ∑ w : Pd4cBoundedWord T B, (pd4c_listDensity ν (pd4c_word w.2) : ℂ) *
          pd4c_listDelta m (pd4c_word w.2) *
            pd4c_groupProjectedKernel ν V q p promoted stored ρ z' z (pd4c_word w.2) l := by
        apply Finset.sum_congr rfl
        intro w hw
        dsimp [G, F, pd4c_listDampedDelta, pd4c_groupProjectedKernel]
        ring
      _ = _ := hev
  rw [hleft, hright] at hpair
  exact hpair

theorem pd4c_groupProjectedKernel_star (ν : Particle → ℝ) (V : ℝ) (p q : Particle)
    (stored promoted : Bool) (ρ : ℝ) (z z' : ℤ × ℤ) (l m : List Particle) :
    star (pd4c_groupProjectedKernel ν V p q stored promoted ρ z z' l m) =
      pd4c_groupProjectedKernel ν V p q stored promoted ρ z z' l m := by
  have hmul (a b : ℂ) (ha : star a = a) (hb : star b = b) : star (a * b) = a * b := by
    rw [star_mul, ha, hb]
    ring
  let F := pd4c_listDampedDelta ρ z' m
  have hF (u : List Particle) : star (F u) = F u := by
    apply hmul
    · simp
    · exact pd4c_listDelta_star m u
  have hretrieve (f : List Particle → ℂ) (hf : ∀ u, star (f u) = f u)
      (u : List Particle) : star (pd4c_listRetrieve q f u) = pd4c_listRetrieve q f u := by
    unfold pd4c_listRetrieve
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hh : u.get k = q
    · simp only [if_pos hh]
      exact hf _
    · simp only [if_neg hh, star_zero]
  have htransfer : star (pd4c_listTransfer ν V p q stored promoted F l) =
      pd4c_listTransfer ν V p q stored promoted F l := by
    cases stored <;> cases promoted
    · exact hmul _ _ (by simp) (hF l)
    · exact hmul _ _ (by simp) (hretrieve F hF l)
    · exact hmul _ _ (by simp) (hF (l ++ [p]))
    · exact hmul _ _ (by simp) (hretrieve (fun u => F (u ++ [p])) (fun u => hF (u ++ [p])) l)
  exact hmul _ _ (by simp) htransfer

end

end ArtinPrimitiveRoots.TypeII.PD
