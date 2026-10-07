import ArtinPrimitiveRoots.TypeII.PD.Memory
import ArtinPrimitiveRoots.TypeII.PD.Determinant
import ArtinPrimitiveRoots.TypeII.Proofs.pd5.Partition
import ArtinPrimitiveRoots.TypeII.Proofs.pd5.Ranks
import ArtinPrimitiveRoots.TypeII.Proofs.pd5.Atoms
import ArtinPrimitiveRoots.TypeII.Proofs.pd5.HistoryPartition
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
set_option autoImplicit false
set_option linter.unusedVariables false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical MeasureTheory Filter
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-! ## §5 Memory results (PD 04:11-966) -/

/-- The lifespan expansion of one prime (mem:orphan-identity, mem:prefix, mem:suffix,
mem:run-charge before the `V_i` factors), PD 04:82-132.  `lam j = [z_j]_p`, `act j` = active at
visit `j`, `eta j = η'_j`, `bp = b'_p`.  No active visit: `1 +` orphan lifespans; active visits
with a common line `λ*`: one lifespan through `[α,γ] = [min A, max A]` with optional ghost
extensions at both ends; disagreeing active lines: `0`. -/
def lifespanSum (p N : ℕ) (lam : Fin (N + 1) → Fin (p + 1)) (act : Fin (N + 1) → Prop)
    (eta : Fin (N + 1) → ℝ) (bp : ℝ) : ℝ :=
  let A : Finset (Fin (N + 1)) := Finset.univ.filter act
  let hit (j : Fin (N + 1)) (l : Fin (p + 1)) : ℝ := if lam j = l then 1 else 0
  if hA : A.Nonempty then
    let α := A.min' hA
    let γ := A.max' hA
    let ls := lam α
    if ∀ j ∈ A, lam j = ls then
      (((p : ℝ) + 1) * bp)⁻¹ *
        (1 - ∑ h ∈ Finset.univ.filter (fun h => h < α),
            eta h * hit h ls * ∏ j ∈ Finset.univ.filter (fun j => h < j ∧ j < α),
              (1 - eta j * hit j ls)) *
        (∏ j ∈ Finset.univ.filter (fun j => α < j ∧ j < γ ∧ j ∉ A), (1 - eta j * hit j ls)) *
        (1 - ∑ h ∈ Finset.univ.filter (fun h => γ < h),
            eta h * hit h ls * ∏ j ∈ Finset.univ.filter (fun j => γ < j ∧ j < h),
              (1 - eta j * hit j ls))
    else 0
  else
    1 + (((p : ℝ) + 1) * bp)⁻¹ *
      ∑ ac ∈ Finset.univ.filter (fun ac : Fin (N + 1) × Fin (N + 1) => ac.1 < ac.2),
        eta ac.1 * eta ac.2 * hit ac.2 (lam ac.1) *
          ∏ j ∈ Finset.univ.filter (fun j => ac.1 < j ∧ j < ac.2), (1 - eta j * hit j (lam ac.1))

private theorem prod_one_sub_telescope {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) :
    (∏ i ∈ s, (1 - f i)) =
      1 - ∑ a ∈ s, f a * ∏ j ∈ s.filter (fun j => a < j), (1 - f j) := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
      by_cases hs : s.Nonempty
      · let m := s.max' hs
        have hm : m ∈ s := Finset.max'_mem s hs
        let t := s.erase m
        have hsub : t ⊂ s := Finset.erase_ssubset hm
        have hmax : ∀ a ∈ t, a < m := by
          intro a ha
          have han : a ≠ m := (Finset.mem_erase.mp ha).1
          have haS : a ∈ s := (Finset.mem_erase.mp ha).2
          have hale : a ≤ m := by simpa [m] using s.le_max' a haS
          exact lt_of_le_of_ne hale han
        have hfilter (a : ι) (ha : a ∈ t) :
            s.filter (fun j => a < j) = insert m (t.filter (fun j => a < j)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hjs, haj⟩
            by_cases hjm : j = m
            · exact Or.inl hjm
            · exact Or.inr ⟨Finset.mem_erase.mpr ⟨hjm, hjs⟩, haj⟩
          · intro hj
            rcases hj with hjm | ⟨hjt, haj⟩
            · subst j
              exact ⟨hm, hmax a ha⟩
            · exact ⟨(Finset.mem_erase.mp hjt).2, haj⟩
        have htail (a : ι) (ha : a ∈ t) :
            (∏ j ∈ s.filter (fun j => a < j), (1 - f j)) =
              (∏ j ∈ t.filter (fun j => a < j), (1 - f j)) * (1 - f m) := by
          rw [hfilter a ha]
          simp [Finset.prod_insert, t]
          ring
        have htailm : ∏ j ∈ s.filter (fun j => m < j), (1 - f j) = 1 := by
          have hfilterm : s.filter (fun j => m < j) = ∅ :=
            Finset.filter_eq_empty_iff.mpr (by
              intro j hjs
              exact not_lt_of_ge (s.le_max' j hjs))
          simp [hfilterm]
        have hprod :
            (∏ i ∈ s, (1 - f i)) = (∏ i ∈ t, (1 - f i)) * (1 - f m) := by
          simpa [t] using (Finset.prod_erase_mul s (fun i => 1 - f i) hm).symm
        let g := fun a => f a * ∏ j ∈ s.filter (fun j => a < j), (1 - f j)
        have hsumSplit :
            (∑ a ∈ s, g a) = (∑ a ∈ t, g a) + g m := by
          simpa [t] using (Finset.sum_erase_add s g hm).symm
        have hsum :
            (∑ a ∈ s, f a * ∏ j ∈ s.filter (fun j => a < j), (1 - f j)) =
              (∑ a ∈ t, f a * ∏ j ∈ t.filter (fun j => a < j), (1 - f j)) *
                  (1 - f m) + f m := by
          calc
            _ = (∑ a ∈ t, g a) + g m := hsumSplit
            _ = (∑ a ∈ t,
                  f a * (∏ j ∈ t.filter (fun j => a < j), (1 - f j)) * (1 - f m)) +
                  f m := by
                congr 1
                · apply Finset.sum_congr rfl
                  intro a ha
                  dsimp [g]
                  rw [htail a ha]
                  ring
                · dsimp [g]
                  rw [htailm]
                  ring
            _ = _ := by
                rw [Finset.sum_mul]
        rw [hprod, hsum, ih t hsub]
        ring
      · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        simp [hs0]

private theorem prod_one_sub_telescope_left {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ) :
    (∏ i ∈ s, (1 - f i)) =
      1 - ∑ a ∈ s, f a * ∏ j ∈ s.filter (fun j => j < a), (1 - f j) := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
      by_cases hs : s.Nonempty
      · let m := s.min' hs
        have hm : m ∈ s := Finset.min'_mem s hs
        let t := s.erase m
        have hsub : t ⊂ s := Finset.erase_ssubset hm
        have hmin : ∀ a ∈ t, m < a := by
          intro a ha
          exact Finset.min'_lt_of_mem_erase_min' s hs ha
        have hfilter (a : ι) (ha : a ∈ t) :
            s.filter (fun j => j < a) = insert m (t.filter (fun j => j < a)) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨hjs, hja⟩
            by_cases hjm : j = m
            · exact Or.inl hjm
            · exact Or.inr ⟨Finset.mem_erase.mpr ⟨hjm, hjs⟩, hja⟩
          · intro hj
            rcases hj with hjm | ⟨hjt, hja⟩
            · subst j
              exact ⟨hm, hmin a ha⟩
            · exact ⟨(Finset.mem_erase.mp hjt).2, hja⟩
        have htail (a : ι) (ha : a ∈ t) :
            (∏ j ∈ s.filter (fun j => j < a), (1 - f j)) =
              (∏ j ∈ t.filter (fun j => j < a), (1 - f j)) * (1 - f m) := by
          rw [hfilter a ha]
          simp [Finset.prod_insert, t]
          ring
        have htailm : ∏ j ∈ s.filter (fun j => j < m), (1 - f j) = 1 := by
          have hfilterm : s.filter (fun j => j < m) = ∅ :=
            Finset.filter_eq_empty_iff.mpr (by
              intro j hjs
              exact not_lt_of_ge (s.min'_le j hjs))
          simp [hfilterm]
        have hprod :
            (∏ i ∈ s, (1 - f i)) = (∏ i ∈ t, (1 - f i)) * (1 - f m) := by
          simpa [t] using (Finset.prod_erase_mul s (fun i => 1 - f i) hm).symm
        let g := fun a => f a * ∏ j ∈ s.filter (fun j => j < a), (1 - f j)
        have hsumSplit :
            (∑ a ∈ s, g a) = (∑ a ∈ t, g a) + g m := by
          simpa [t] using (Finset.sum_erase_add s g hm).symm
        have hsum :
            (∑ a ∈ s, f a * ∏ j ∈ s.filter (fun j => j < a), (1 - f j)) =
              (∑ a ∈ t, f a * ∏ j ∈ t.filter (fun j => j < a), (1 - f j)) *
                  (1 - f m) + f m := by
          calc
            _ = (∑ a ∈ t, g a) + g m := hsumSplit
            _ = (∑ a ∈ t,
                  f a * (∏ j ∈ t.filter (fun j => j < a), (1 - f j)) * (1 - f m)) +
                  f m := by
                congr 1
                · apply Finset.sum_congr rfl
                  intro a ha
                  dsimp [g]
                  rw [htail a ha]
                  ring
                · dsimp [g]
                  rw [htailm]
                  ring
            _ = _ := by
                rw [Finset.sum_mul]
        rw [hprod, hsum, ih t hsub]
        ring
      · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
        simp [hs0]

/-- `t2:pd.prime-lifespan` (new node, general) — PD 04:68-115.  The primewise identity:
the independent-line factor of one prime equals `b'_p` times its lifespan expansion.  Proof:
expand the product; singletons give `b'_p`; for larger sets fix first and last index (orphan
case); for active primes only the common line survives and the outer products telescope. -/
theorem prime_lifespan (p N : ℕ) (lam : Fin (N + 1) → Fin (p + 1))
    (act : Fin (N + 1) → Prop) (eta : Fin (N + 1) → ℝ) (bp : ℝ)
    (hbp : bp = 1 - ∑ j : Fin (N + 1), eta j / ((p : ℝ) + 1)) (hbp0 : bp ≠ 0) :
    ((p : ℝ) + 1)⁻¹ * ∑ l : Fin (p + 1), ∏ j : Fin (N + 1),
        (if act j then (if lam j = l then (1 : ℝ) else 0)
          else 1 - eta j * (if lam j = l then 1 else 0)) =
      bp * lifespanSum p N lam act eta bp := by
  classical
  let I : Finset (Fin (N + 1)) := Finset.univ
  let A : Finset (Fin (N + 1)) := I.filter act
  let hit (j : Fin (N + 1)) (l : Fin (p + 1)) : ℝ := if lam j = l then 1 else 0
  let suffix (a : Fin (N + 1)) (l : Fin (p + 1)) : ℝ :=
    ∏ j ∈ I.filter (fun j => a < j), (1 - eta j * hit j l)
  let pplus : ℝ := (p : ℝ) + 1
  have hpplus : 0 < pplus := by positivity
  have hpplus0 : pplus ≠ 0 := ne_of_gt hpplus
  have hbase : pplus * bp = pplus - ∑ j : Fin (N + 1), eta j := by
    dsimp [pplus]
    rw [hbp]
    rw [mul_sub, Finset.mul_sum]
    rw [mul_one]
    apply congrArg (fun x : ℝ => (↑p + 1) - x)
    apply Finset.sum_congr rfl
    intro j hj
    field_simp [hpplus0]
  by_cases hA : A.Nonempty
  · let α := A.min' hA
    let γ := A.max' hA
    let ls := lam α
    have hαA : α ∈ A := by exact Finset.min'_mem A hA
    have hγA : γ ∈ A := by exact Finset.max'_mem A hA
    have hαact : act α := by simpa [A, I] using hαA
    have hγact : act γ := by simpa [A, I] using hγA
    by_cases hcommon : ∀ j ∈ A, lam j = ls
    · have hlineprod (l : Fin (p + 1)) :
          (∏ j : Fin (N + 1),
            (if act j then (if lam j = l then (1 : ℝ) else 0)
              else 1 - eta j * hit j l)) =
            if l = ls then
              ∏ j ∈ I.filter (fun j => ¬ act j), (1 - eta j * hit j ls) else 0 := by
        by_cases hl : l = ls
        · subst l
          have hterm (j : Fin (N + 1)) :
              (if act j then (if lam j = ls then (1 : ℝ) else 0)
                else 1 - eta j * hit j ls) =
              if act j then 1 else 1 - eta j * hit j ls := by
            by_cases hj : act j
            · have hjA : j ∈ A := by simp [A, I, hj]
              simp [hj, hcommon j hjA]
            · simp [hj]
          simp_rw [hterm]
          rw [Finset.prod_filter]
          simp [I]
        · have hzero :
              (∏ j : Fin (N + 1),
                (if act j then (if lam j = l then (1 : ℝ) else 0)
                  else 1 - eta j * hit j l)) = 0 := by
            apply Finset.prod_eq_zero (Finset.mem_univ α)
            have hneq : lam α ≠ l := by
              intro hEq
              apply hl
              simpa [ls] using hEq.symm
            simp [hαact, hneq]
          simp [hzero, hl]
      have hinactiveProd :
          ∑ l : Fin (p + 1),
            ∏ j : Fin (N + 1),
              (if act j then (if lam j = l then (1 : ℝ) else 0)
                else 1 - eta j * hit j l) =
            ∏ j ∈ I.filter (fun j => ¬ act j), (1 - eta j * hit j ls) := by
        simp_rw [hlineprod]
        simp
      let pre : Finset (Fin (N + 1)) := I.filter (fun j => j < α)
      let mid : Finset (Fin (N + 1)) :=
        I.filter (fun j => α < j ∧ j < γ ∧ j ∉ A)
      let post : Finset (Fin (N + 1)) := I.filter (fun j => γ < j)
      let inactive : Finset (Fin (N + 1)) := I.filter (fun j => ¬ act j)
      have hminle (j : Fin (N + 1)) (hj : j ∈ A) : α ≤ j :=
        Finset.min'_le A j hj
      have hlemax (j : Fin (N + 1)) (hj : j ∈ A) : j ≤ γ :=
        Finset.le_max' A j hj
      have hpartsSet : inactive = (pre ∪ mid) ∪ post := by
        ext j
        simp only [inactive, pre, mid, post, Finset.mem_filter, Finset.mem_union,
          I, Finset.mem_univ, true_and]
        constructor
        · intro hnot
          by_cases hpre : j < α
          · exact Or.inl (Or.inl hpre)
          · by_cases hpost : γ < j
            · exact Or.inr hpost
            · have hαle : α ≤ j := le_of_not_gt hpre
              have hjγ : j ≤ γ := le_of_not_gt hpost
              have hja : j ≠ α := by
                intro hEq
                subst j
                exact hnot hαact
              have hgj : j ≠ γ := by
                intro hEq
                subst j
                exact hnot hγact
              have hjA : j ∉ A := by
                intro hjA
                exact hnot (by simpa [A, I] using hjA)
              exact Or.inl (Or.inr ⟨lt_of_le_of_ne hαle (Ne.symm hja),
                lt_of_le_of_ne hjγ hgj, hjA⟩)
        · intro h
          rcases h with (hpre | hmid) | hpost
          · intro hj
            have hjA : j ∈ A := by simpa [A, I] using hj
            exact (not_lt_of_ge (hminle j hjA)) hpre
          · intro hj
            have hjA : j ∈ A := by simpa [A, I] using hj
            exact hmid.2.2 hjA
          · intro hj
            have hjA : j ∈ A := by simpa [A, I] using hj
            exact (not_lt_of_ge (hlemax j hjA)) hpost
      have hdisj₁ : Disjoint pre mid := by
        apply Finset.disjoint_left.mpr
        intro j hjpre hjmid
        have hjpre' : j < α := by simpa [pre, I] using hjpre
        have hjmid' : α < j ∧ j < γ ∧ j ∉ A := by simpa [mid, I] using hjmid
        exact (not_lt_of_ge (le_of_lt hjpre')) hjmid'.1
      have hdisj₂ : Disjoint (pre ∪ mid) post := by
        apply Finset.disjoint_left.mpr
        intro j hjrest hjpost
        have hjpost' : γ < j := by simpa [post, I] using hjpost
        rcases Finset.mem_union.mp hjrest with hjpre | hjmid
        · have hjpre' : j < α := by simpa [pre, I] using hjpre
          have hαγ : α ≤ γ := Finset.min'_le_max' A hA
          exact (not_lt_of_ge (le_of_lt hjpost')) (lt_of_lt_of_le hjpre' hαγ)
        · have hjmid' : α < j ∧ j < γ ∧ j ∉ A := by simpa [mid, I] using hjmid
          exact (not_lt_of_ge (le_of_lt hjpost')) hjmid'.2.1
      have hparts :
          (∏ j ∈ inactive, (1 - eta j * hit j ls)) =
            (∏ j ∈ pre, (1 - eta j * hit j ls)) *
            (∏ j ∈ mid, (1 - eta j * hit j ls)) *
              (∏ j ∈ post, (1 - eta j * hit j ls)) := by
        rw [hpartsSet, Finset.prod_union hdisj₂, Finset.prod_union hdisj₁]
      have hprefix :
          1 - ∑ h ∈ I.filter (fun h => h < α),
              eta h * hit h ls *
                ∏ j ∈ I.filter (fun j => h < j ∧ j < α),
                  (1 - eta j * hit j ls) =
            ∏ j ∈ pre, (1 - eta j * hit j ls) := by
        have ht := prod_one_sub_telescope pre (fun j => eta j * hit j ls)
        simpa [pre, I, Finset.filter_filter, and_assoc, and_left_comm, and_comm] using ht.symm
      have hsuffix :
          1 - ∑ h ∈ I.filter (fun h => γ < h),
              eta h * hit h ls *
                ∏ j ∈ I.filter (fun j => γ < j ∧ j < h),
                  (1 - eta j * hit j ls) =
            ∏ j ∈ post, (1 - eta j * hit j ls) := by
        have ht := prod_one_sub_telescope_left post (fun j => eta j * hit j ls)
        simpa [post, I, Finset.filter_filter, and_assoc, and_left_comm, and_comm] using ht.symm
      have hcommon' : ∀ j : Fin (N + 1), act j → lam j = ls := by
        intro j hj
        apply hcommon
        simp [A, I, hj]
      have hlife :
          lifespanSum p N lam act eta bp =
            (pplus * bp)⁻¹ *
              (∏ j ∈ pre, (1 - eta j * hit j ls)) *
              (∏ j ∈ mid, (1 - eta j * hit j ls)) *
              (∏ j ∈ post, (1 - eta j * hit j ls)) := by
        simp only [lifespanSum, A, I, dif_pos hA, if_pos hcommon', α, γ, ls, hit,
          pre, mid, post, Finset.mem_filter, Finset.mem_univ, true_and,
          hprefix, hsuffix, pplus]
      rw [show (∏ j ∈ I.filter (fun j => ¬ act j), (1 - eta j * hit j ls)) =
          (∏ j ∈ inactive, (1 - eta j * hit j ls)) by rfl] at hinactiveProd
      rw [hinactiveProd, hlife, hparts]
      field_simp [hpplus0, hbp0, mul_ne_zero hpplus0 hbp0] <;>
        (dsimp [pplus]; ring)
    · have hdisagree : ∃ j ∈ A, lam j ≠ ls := by
        by_contra h
        push_neg at h
        exact hcommon h
      obtain ⟨j, hjA, hjline⟩ := hdisagree
      have hjact : act j := by simpa [A, I] using hjA
      have hzero (l : Fin (p + 1)) :
          ∏ j' : Fin (N + 1),
            (if act j' then (if lam j' = l then (1 : ℝ) else 0)
              else 1 - eta j' * hit j' l) = 0 := by
        by_cases hl : l = ls
        · apply Finset.prod_eq_zero (Finset.mem_univ j)
          have hneq : lam j ≠ l := by
            intro hEq
            apply hjline
            calc
              lam j = l := hEq
              _ = ls := hl
          simp [hjact, hneq]
        · apply Finset.prod_eq_zero (Finset.mem_univ α)
          have hneq : lam α ≠ l := by
            intro hEq
            apply hl
            simpa [ls] using hEq.symm
          simp [hαact, hneq]
      have hsumzero :
          ∑ l : Fin (p + 1),
            ∏ j' : Fin (N + 1),
              (if act j' then (if lam j' = l then (1 : ℝ) else 0)
                else 1 - eta j' * hit j' l) = 0 := by
        simp [hzero]
      have hnoCommon : ¬ ∀ k : Fin (N + 1), act k → lam k = ls := by
        intro hc
        exact hjline (hc j hjact)
      have hsumzero' :
          ∑ l : Fin (p + 1),
            ∏ j' : Fin (N + 1),
              (if act j' then (if lam j' = l then (1 : ℝ) else 0)
                else 1 - (if lam j' = l then eta j' else 0)) = 0 := by
        simpa [hit] using hsumzero
      simp [lifespanSum, A, I, α, γ, ls, hA, hnoCommon, pplus, hpplus0]
      rw [hsumzero']
  · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    have hno : ∀ j : Fin (N + 1), ¬ act j := by
      intro j hj
      have hjA : j ∈ A := by simp [A, I, hj]
      simp [hAempty] at hjA
    have hpoint (l : Fin (p + 1)) :
        (∏ j : Fin (N + 1),
          (if act j then (if lam j = l then (1 : ℝ) else 0)
            else 1 - eta j * hit j l)) =
          1 - ∑ a ∈ I, eta a * hit a l * suffix a l := by
      have ht := prod_one_sub_telescope I (fun j => eta j * hit j l)
      simpa [I, hit, suffix, hno] using ht
    have hsingle (a : Fin (N + 1)) :
        ∑ l : Fin (p + 1), hit a l * suffix a l = suffix a (lam a) := by
      simp [hit, suffix, eq_comm]
    have hdouble :
        (∑ l : Fin (p + 1), ∑ a ∈ I, eta a * hit a l * suffix a l) =
          ∑ a ∈ I, eta a * suffix a (lam a) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      calc
        (∑ l : Fin (p + 1), eta a * hit a l * suffix a l) =
            ∑ l : Fin (p + 1), eta a * (hit a l * suffix a l) := by
              apply Finset.sum_congr rfl
              intro l hl
              ring
        _ = eta a * (∑ l : Fin (p + 1), hit a l * suffix a l) := by
              rw [Finset.mul_sum]
        _ = eta a * suffix a (lam a) := by rw [hsingle a]
    have hlineSum :
        (∑ l : Fin (p + 1),
          ∏ j : Fin (N + 1),
            (if act j then (if lam j = l then (1 : ℝ) else 0)
              else 1 - eta j * hit j l)) =
          pplus - ∑ a ∈ I, eta a * suffix a (lam a) := by
      calc
        _ = ∑ l : Fin (p + 1), (1 - ∑ a ∈ I, eta a * hit a l * suffix a l) := by
              apply Finset.sum_congr rfl
              intro l hl
              rw [hpoint l]
        _ = (∑ l : Fin (p + 1), (1 : ℝ)) -
              ∑ l : Fin (p + 1), ∑ a ∈ I, eta a * hit a l * suffix a l := by
              rw [Finset.sum_sub_distrib]
        _ = pplus - ∑ a ∈ I, eta a * suffix a (lam a) := by
              rw [hdouble]
              simp [pplus]
    have hsuffix (a : Fin (N + 1)) :
        1 - suffix a (lam a) =
          ∑ c ∈ I.filter (fun c => a < c),
            eta c * hit c (lam a) *
              ∏ j ∈ I.filter (fun j => a < j ∧ j < c),
                (1 - eta j * hit j (lam a)) := by
      have ht := prod_one_sub_telescope_left (I.filter (fun j => a < j))
        (fun j => eta j * hit j (lam a))
      have ht' : suffix a (lam a) =
          1 - ∑ c ∈ I.filter (fun c => a < c),
            eta c * hit c (lam a) *
              ∏ j ∈ I.filter (fun j => a < j ∧ j < c),
                (1 - eta j * hit j (lam a)) := by
        simpa [suffix, Finset.filter_filter, and_assoc, and_left_comm, and_comm] using ht
      rw [ht']
      ring
    let pairSet : Finset (Fin (N + 1) × Fin (N + 1)) :=
      Finset.univ.filter (fun ac => ac.1 < ac.2)
    let pairTerm (a c : Fin (N + 1)) : ℝ :=
      eta a * eta c * hit c (lam a) *
        ∏ j ∈ I.filter (fun j => a < j ∧ j < c), (1 - eta j * hit j (lam a))
    have hpairReindex :
        (∑ ac ∈ pairSet, pairTerm ac.1 ac.2) =
          ∑ a ∈ I, ∑ c ∈ I.filter (fun c => a < c), pairTerm a c := by
      simpa [pairSet, I, pairTerm] using
        (Finset.sum_finset_product
          (r := pairSet) (s := I) (t := fun a => I.filter (fun c => a < c))
          (by intro ac; simp [pairSet, I]))
    have hpair :
        (∑ a ∈ I, eta a * (1 - suffix a (lam a))) = ∑ ac ∈ pairSet, pairTerm ac.1 ac.2 := by
      calc
        _ = ∑ a ∈ I, eta a *
              (∑ c ∈ I.filter (fun c => a < c),
                eta c * hit c (lam a) *
                  ∏ j ∈ I.filter (fun j => a < j ∧ j < c),
                    (1 - eta j * hit j (lam a))) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [hsuffix a]
        _ = ∑ a ∈ I, ∑ c ∈ I.filter (fun c => a < c), pairTerm a c := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro c hc
              simp [pairTerm, mul_assoc]
        _ = ∑ ac ∈ pairSet, pairTerm ac.1 ac.2 := hpairReindex.symm
    have hsumAux :
        (∑ a ∈ I, eta a * suffix a (lam a)) =
          (∑ a ∈ I, eta a) - ∑ ac ∈ pairSet, pairTerm ac.1 ac.2 := by
      rw [← hpair, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      ring
    have hsum :
        (∑ l : Fin (p + 1),
          ∏ j : Fin (N + 1),
            (if act j then (if lam j = l then (1 : ℝ) else 0)
              else 1 - eta j * hit j l)) =
          (pplus * bp) + ∑ ac ∈ pairSet, pairTerm ac.1 ac.2 := by
      calc
        _ = pplus - ∑ a ∈ I, eta a * suffix a (lam a) := hlineSum
        _ = (pplus - ∑ a ∈ I, eta a) + ∑ ac ∈ pairSet, pairTerm ac.1 ac.2 := by
              rw [hsumAux]
              ring
        _ = (pplus * bp) + ∑ ac ∈ pairSet, pairTerm ac.1 ac.2 := by rw [hbase]
    have hsumFinal :
        (∑ l : Fin (p + 1),
          ∏ j : Fin (N + 1),
            (if act j then (if lam j = l then (1 : ℝ) else 0)
              else 1 - eta j * hit j l)) =
          pplus * bp +
            ∑ ac ∈ Finset.univ.filter
                (fun ac : Fin (N + 1) × Fin (N + 1) => ac.1 < ac.2),
              eta ac.1 * eta ac.2 * hit ac.2 (lam ac.1) *
                ∏ j ∈ Finset.univ.filter (fun j => ac.1 < j ∧ j < ac.2),
                  (1 - eta j * hit j (lam ac.1)) := by
      simpa [pairSet, pairTerm, I] using hsum
    rw [hsumFinal]
    simp [lifespanSum, hA, A, I, hit, pplus]
    field_simp [hpplus0, hbp0, mul_ne_zero hpplus0 hbp0] <;> ring

/-- The lifespan expansion of a group prime along a line-model path. -/
def pathLifespan {K : ℕ} (F : PDFix K) (S : PDScale) (γ : EnvPath S.x K) (p : ℕ) : ℝ :=
  lifespanSum p (pathLength S.x) (fun j => projLine p (γ j).1) (IsActiveAt γ p)
    (fun j => memoryEta S.x F.q_d j.val) (memoryBPrime S.x F.q_d p)

private theorem envPoint_band_box_finite {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (hU : 0 < S.U) (hV : 0 < S.V) (hw : w.InRegion S) :
    {s : EnvPoint S.x K | (∀ i j, s.2 i j ∈ primeBand S.x (F.a i)) ∧
      envBox S w s.1}.Finite := by
  classical
  rcases hw with ⟨huL, huR, hvL, hvR, hrL, hrU⟩
  have hu : 0 < w.u := lt_of_lt_of_le hU huL
  have hv : 0 < w.v := lt_of_lt_of_le hV hvL
  let M : ℝ := 16 + 500 * S.U * S.V
  let n : ℕ := ⌈M⌉₊
  have hM : 0 < M := by dsimp [M]; positivity
  have hn : M ≤ (n : ℝ) := by simpa [n] using (Nat.le_ceil M)
  have hUV : 0 < S.U * S.V := mul_pos hU hV
  let I : Set ℤ := Set.Icc (-(n : ℤ)) (n : ℤ)
  let Z : Set (ℤ × ℤ) := {z | envBox S w z}
  have hZsub : Z ⊆ I ×ˢ I := by
    intro z hz
    have hτlo' : S.U / w.u ≤ w.tau z := by
      apply (div_le_iff₀ hu).2
      simpa [mul_comm] using hz.1
    have hτlo : (1 / 16 : ℝ) ≤ w.tau z := by
      have haux : (1 / 16 : ℝ) ≤ S.U / w.u := by
        apply (le_div_iff₀ hu).2
        nlinarith
      exact haux.trans hτlo'
    have hτhi' : w.tau z ≤ (16 * S.U) / w.u := by
      apply (le_div_iff₀ hu).2
      simpa [mul_comm] using hz.2.1
    have hτhi : w.tau z ≤ 16 := by
      calc
        w.tau z ≤ (16 * S.U) / w.u := hτhi'
        _ ≤ 16 := by
          apply (div_le_iff₀ hu).2
          nlinarith
    have hτpos : 0 < w.tau z := by linarith
    have hvtau : 0 ≤ w.v * w.tau z := (mul_nonneg hv.le hτpos.le)
    have hvtauU : w.v * w.tau z ≤ 32 * S.V := by
      calc
        w.v * w.tau z ≤ w.v * 16 := mul_le_mul_of_nonneg_left hτhi hv.le
        _ ≤ (2 * S.V) * 16 := mul_le_mul_of_nonneg_right hvR (by norm_num)
        _ = 32 * S.V := by ring
    have hz2lo' : -31 * S.V ≤ (z.2 : ℝ) / w.u := by
      have h := hz.2.2.1
      linarith
    have hz2hi' : (z.2 : ℝ) / w.u ≤ 2 * S.V := by
      have h := hz.2.2.2
      linarith
    have hz2lo : (-31 * S.V) * w.u ≤ (z.2 : ℝ) :=
      (le_div_iff₀ hu).mp hz2lo'
    have hz2hi : (z.2 : ℝ) ≤ (2 * S.V) * w.u :=
      (div_le_iff₀ hu).mp hz2hi'
    have hz2loB : -(496 * S.U * S.V) ≤ (z.2 : ℝ) := by
      calc
        -(496 * S.U * S.V) = (-31 * S.V) * (16 * S.U) := by ring
        _ ≤ (-31 * S.V) * w.u :=
          mul_le_mul_of_nonpos_left huR (by nlinarith [hV])
        _ ≤ (z.2 : ℝ) := hz2lo
    have hz2hiB : (z.2 : ℝ) ≤ 32 * S.U * S.V := by
      calc
        (z.2 : ℝ) ≤ (2 * S.V) * w.u := hz2hi
        _ ≤ (2 * S.V) * (16 * S.U) :=
          mul_le_mul_of_nonneg_left huR (by positivity)
        _ = 32 * S.U * S.V := by ring
    have hz2Real : |(z.2 : ℝ)| ≤ M := by
      rw [abs_le]
      constructor
      · dsimp [M]
        linarith [hz2loB, hUV]
      · dsimp [M]
        linarith [hz2hiB, hUV]
    have hrzlo : -(496 * S.U * S.V) ≤ w.r * (z.2 : ℝ) := by
      by_cases hz20 : 0 ≤ (z.2 : ℝ)
      · have h := mul_nonneg hrL hz20
        linarith [hUV]
      · have hrle : w.r - 1 ≤ 0 := by linarith [hrU]
        have hz2le : (z.2 : ℝ) ≤ 0 := le_of_lt (lt_of_not_ge hz20)
        have h := mul_nonneg_of_nonpos_of_nonpos hrle hz2le
        linarith [hz2loB]
    have hrzhi : w.r * (z.2 : ℝ) ≤ 496 * S.U * S.V := by
      by_cases hz20 : 0 ≤ (z.2 : ℝ)
      · have hrOne : 0 ≤ 1 - w.r := by linarith [hrU]
        have h := mul_nonneg hrOne hz20
        nlinarith [hz2hiB]
      · have h := mul_nonpos_of_nonneg_of_nonpos hrL (le_of_lt (lt_of_not_ge hz20))
        nlinarith [hUV]
    have hz1lo : -(496 * S.U * S.V) ≤ (z.1 : ℝ) := by
      have ht : w.tau z = (z.1 : ℝ) + w.r * (z.2 : ℝ) := rfl
      linarith [ht, hτlo, hrzhi]
    have hz1hi : (z.1 : ℝ) ≤ 16 + 496 * S.U * S.V := by
      have ht : w.tau z = (z.1 : ℝ) + w.r * (z.2 : ℝ) := rfl
      linarith [ht, hτhi, hrzlo]
    have hz1Real : |(z.1 : ℝ)| ≤ M := by
      rw [abs_le]
      constructor <;> dsimp [M] <;> linarith [hz1lo, hz1hi, hUV]
    have hn1loR : -(n : ℝ) ≤ (z.1 : ℝ) :=
      (by linarith [hn] : -(n : ℝ) ≤ -M).trans (abs_le.mp hz1Real).1
    have hn1hiR : (z.1 : ℝ) ≤ (n : ℝ) := (abs_le.mp hz1Real).2.trans hn
    have hn2loR : -(n : ℝ) ≤ (z.2 : ℝ) :=
      (by linarith [hn] : -(n : ℝ) ≤ -M).trans (abs_le.mp hz2Real).1
    have hn2hiR : (z.2 : ℝ) ≤ (n : ℝ) := (abs_le.mp hz2Real).2.trans hn
    have hn1lo : -(n : ℤ) ≤ z.1 := by exact_mod_cast hn1loR
    have hn1hi : z.1 ≤ (n : ℤ) := by exact_mod_cast hn1hiR
    have hn2lo : -(n : ℤ) ≤ z.2 := by exact_mod_cast hn2loR
    have hn2hi : z.2 ≤ (n : ℤ) := by exact_mod_cast hn2hiR
    constructor
    · simpa [I, Set.mem_Icc] using ⟨hn1lo, hn1hi⟩
    · simpa [I, Set.mem_Icc] using ⟨hn2lo, hn2hi⟩
  have hZ : Z.Finite := (Set.finite_Icc _ _).prod (Set.finite_Icc _ _) |>.subset hZsub
  let P : Finset (PrimeLists S.x K) :=
    Fintype.piFinset fun i : Fin K =>
      Fintype.piFinset fun j : Fin (slotCount S.x) => primeBand S.x (F.a i)
  have hP (p : PrimeLists S.x K)
      (hp : ∀ i j, p i j ∈ primeBand S.x (F.a i)) : p ∈ P := by
    simp only [P, Fintype.mem_piFinset]
    intro i j
    exact hp i j
  have hset :
      {s : EnvPoint S.x K | (∀ i j, s.2 i j ∈ primeBand S.x (F.a i)) ∧
        envBox S w s.1} ⊆ Z ×ˢ (P : Set (PrimeLists S.x K)) := by
    intro s hs
    exact ⟨hs.2, Finset.mem_coe.mpr (hP s.2 hs.1)⟩
  exact (hZ.prod P.finite_toSet).subset hset

private theorem envPoint_valid_box_finite {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (hU : 0 < S.U) (hV : 0 < S.V) (hw : w.InRegion S) :
    {s : EnvPoint S.x K | EnvValid F S s ∧ envBox S w s.1}.Finite := by
  apply (envPoint_band_box_finite F S w hU hV hw).subset
  intro s hs
  exact ⟨fun i j => (hs.1.2.1 i j).2, hs.2⟩

private def historyDefaultPoint {x : ℝ} {K : ℕ} : EnvPoint x K :=
  ((0, 0), fun _ _ => 0)

private def historyDefaultPath {x : ℝ} {K : ℕ} : EnvPath x K :=
  fun _ => historyDefaultPoint

private def historyRouteIndex {x : ℝ} (k : ℕ) : Fin (pathLength x + 1) :=
  ⟨pathLength x - k, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

private noncomputable def historyRouteFinset {x : ℝ} {K : ℕ}
    (P : Finset (EnvPoint x K)) (k : ℕ) : Finset (EnvPath x K) :=
  Fintype.piFinset fun j : Fin (pathLength x + 1) =>
    if pathLength x - k ≤ j.val then P else {historyDefaultPoint}

private theorem mem_historyRouteFinset {x : ℝ} {K : ℕ}
    (P : Finset (EnvPoint x K)) (k : ℕ) (γ : EnvPath x K) :
    γ ∈ historyRouteFinset P k ↔
      (∀ j, pathLength x - k ≤ j.val → γ j ∈ P) ∧
      (∀ j, j.val < pathLength x - k → γ j = historyDefaultPoint) := by
  simp only [historyRouteFinset, Fintype.mem_piFinset]
  constructor
  · intro h
    constructor
    · intro j hj
      simpa [hj] using h j
    · intro j hj
      have hnot : ¬ pathLength x - k ≤ j.val := by omega
      simpa [hnot] using h j
  · rintro ⟨hP, hD⟩ j
    by_cases hj : pathLength x - k ≤ j.val
    · simpa [hj] using hP j hj
    · simpa [hj] using hD j (by omega)

private theorem historyRouteFinset_zero_sum {x : ℝ} {K : ℕ}
    (P : Finset (EnvPoint x K)) (f : EnvPath x K → ℂ) :
    (∑ γ ∈ historyRouteFinset P 0, f γ) =
      ∑ e ∈ P, f (Function.update historyDefaultPath (Fin.last (pathLength x)) e) := by
  classical
  refine Finset.sum_bij
    (fun γ _ => γ (Fin.last (pathLength x)))
    ?_ ?_ ?_ ?_
  · intro γ hγ
    exact (mem_historyRouteFinset P 0 γ).mp hγ |>.1 _ (by simp)
  · intro γ₁ h₁ γ₂ h₂ he
    have h₁' := (mem_historyRouteFinset P 0 γ₁).mp h₁
    have h₂' := (mem_historyRouteFinset P 0 γ₂).mp h₂
    funext j
    by_cases hj : j = Fin.last (pathLength x)
    · simpa [hj] using he
    · have hjlt : j.val < pathLength x := by
        have hle : j.val ≤ pathLength x := by omega
        have hne : j.val ≠ pathLength x := by
          intro hval
          apply hj
          exact Fin.ext hval
        omega
      rw [h₁'.2 j hjlt, h₂'.2 j hjlt]
  · intro e he
    let γ := Function.update historyDefaultPath (Fin.last (pathLength x)) e
    refine ⟨γ, ?_, ?_⟩
    · rw [mem_historyRouteFinset]
      constructor
      · intro j hj
        have hjlast : j = Fin.last (pathLength x) := by
          apply Fin.ext
          simp only [Fin.val_last]
          omega
        subst j
        simpa [γ] using he
      · intro j hj
        have hjne : j ≠ Fin.last (pathLength x) := by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.val_last] at this
          omega
        simp [γ, historyDefaultPath, Function.update_of_ne hjne]
    · simp [γ]
  · intro γ hγ
    have hγ' := (mem_historyRouteFinset P 0 γ).mp hγ
    have hEq : γ = Function.update historyDefaultPath (Fin.last (pathLength x))
        (γ (Fin.last (pathLength x))) := by
      funext j
      by_cases hj : j = Fin.last (pathLength x)
      · subst j
        simp
      · have hjlt : j.val < pathLength x := by
          have hle : j.val ≤ pathLength x := by omega
          have hne : j.val ≠ pathLength x := by
            intro heq
            apply hj
            exact Fin.ext heq
          omega
        have hdef := hγ'.2 j hjlt
        simp [historyDefaultPath, Function.update_of_ne hj, hdef]
    exact congrArg f hEq

private theorem historyRouteFinset_succ_sum {x : ℝ} {K : ℕ}
    (P : Finset (EnvPoint x K)) (k : ℕ) (hk : k < pathLength x)
    (f : EnvPath x K → ℂ) :
    (∑ γ ∈ historyRouteFinset P (k + 1), f γ) =
      ∑ e ∈ P, ∑ γ ∈ historyRouteFinset P k,
        f (Function.update γ (historyRouteIndex (k + 1)) e) := by
  classical
  let idx := historyRouteIndex (x := x) (k + 1)
  have hidxval : idx.val = pathLength x - (k + 1) := rfl
  have hidxlt : idx.val < pathLength x - k := by
    dsimp [idx, historyRouteIndex]
    omega
  rw [← Finset.sum_product']
  refine Finset.sum_bij
    (fun γ _ => (γ idx, Function.update γ idx historyDefaultPoint))
    ?_ ?_ ?_ ?_
  · intro γ hγ
    have hγ' := (mem_historyRouteFinset P (k + 1) γ).mp hγ
    apply Finset.mem_product.mpr
    constructor
    · exact hγ'.1 idx (by simp [idx, historyRouteIndex])
    · rw [mem_historyRouteFinset]
      constructor
      · intro j hj
        by_cases hji : j = idx
        · subst j
          exact False.elim (not_le_of_gt hidxlt hj)
        · have hj' : pathLength x - (k + 1) ≤ j.val := by
            dsimp [idx, historyRouteIndex] at hji
            omega
          have hmem := hγ'.1 j hj'
          simpa [Function.update_of_ne hji] using hmem
      · intro j hj
        by_cases hji : j = idx
        · subst j
          simp [idx, historyRouteIndex]
        · have hj' : j.val < pathLength x - (k + 1) := by
            have hjiVal : j.val ≠ idx.val := by
              intro heq
              apply hji
              exact Fin.ext heq
            omega
          have hdef := hγ'.2 j hj'
          simpa [Function.update_of_ne hji] using hdef
  · intro γ₁ h₁ γ₂ h₂ heq
    have he : γ₁ idx = γ₂ idx := congrArg Prod.fst heq
    have hrest : Function.update γ₁ idx historyDefaultPoint =
        Function.update γ₂ idx historyDefaultPoint := congrArg Prod.snd heq
    funext j
    by_cases hji : j = idx
    · simpa [hji] using he
    · have h := congrFun hrest j
      simpa [Function.update_of_ne hji] using h
  · intro pair hp
    rcases Finset.mem_product.mp hp with ⟨he, hγ⟩
    let γ := Function.update pair.2 idx pair.1
    refine ⟨γ, ?_, ?_⟩
    · rw [mem_historyRouteFinset]
      constructor
      · intro j hj
        by_cases hji : j = idx
        · subst j
          simpa [γ, idx] using he
        · have hj' : pathLength x - k ≤ j.val := by
            have hjiVal : j.val ≠ idx.val := by
              intro heq
              apply hji
              exact Fin.ext heq
            omega
          have hγprop := (mem_historyRouteFinset P k pair.2).mp hγ
          have hmem := hγprop.1 j hj'
          simpa [γ, Function.update_of_ne hji] using hmem
      · intro j hj
        by_cases hji : j = idx
        · subst j
          have : ¬ idx.val < pathLength x - (k + 1) := by omega
          exact False.elim (this hj)
        · have hj' : j.val < pathLength x - k := by
            dsimp [idx, historyRouteIndex] at hji
            omega
          have hγprop := (mem_historyRouteFinset P k pair.2).mp hγ
          have hdef := hγprop.2 j hj'
          simpa [γ, Function.update_of_ne hji] using hdef
    · apply Prod.ext
      · simp [γ]
      · have hγprop := (mem_historyRouteFinset P k pair.2).mp hγ
        have hdefault : pair.2 idx = historyDefaultPoint := hγprop.2 idx hidxlt
        funext j
        by_cases hji : j = idx
        · subst j
          simp [γ, hdefault]
        · simp [γ, Function.update_of_ne hji]
  · intro γ hγ
    have hγ' := (mem_historyRouteFinset P (k + 1) γ).mp hγ
    have hreconstruct : γ = Function.update
        (Function.update γ idx historyDefaultPoint) idx (γ idx) := by
      funext j
      by_cases hji : j = idx <;> simp [hji]
    exact congrArg f hreconstruct

private theorem validPrimeLists_permute {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (p : PrimeLists x K)
    (hp : ValidPrimeLists x K a p) : ValidPrimeLists x K a (permuteLists σ p) := by
  constructor
  · intro i j
    exact hp.1 i (σ i j)
  · intro i j j' hj
    apply hp.2 i (σ i j) (σ i j')
    intro h
    exact hj ((σ i).injective h)

private theorem edgeAdmissible_target_valid_box {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) {s : MemPoint S.x K}
    {c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i} {z' : ℤ × ℤ}
    (h : EdgeAdmissible F S w s c z') :
    EnvValid F S (z', edgeTargetLists F S s c) ∧ envBox S w z' := by
  rcases h with ⟨_, _, hLists, _, _, hGcd, _, hBox, _, _⟩
  exact ⟨⟨hGcd, hLists⟩, hBox⟩

private theorem tsum_sum_finite_support {α ι : Type*} (T : Finset α) (s : Finset ι)
    (f : α → ι → ℂ) (hzero : ∀ i a, a ∉ T → f a i = 0) :
    (∑' a, ∑ i ∈ s, f a i) = ∑ i ∈ s, ∑' a, f a i := by
  calc
    _ = ∑ a ∈ T, ∑ i ∈ s, f a i := by
      apply tsum_eq_sum
      intro a ha
      simp [hzero _ _ ha]
    _ = ∑ i ∈ s, ∑ a ∈ T, f a i := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      symm
      apply tsum_eq_sum
      intro a ha
      exact hzero i a ha

private theorem edgeAdmissible_position_mem {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) {s : MemPoint S.x K}
    {c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i} {z' : ℤ × ℤ}
    {P : Finset (EnvPoint S.x K)}
    (hP : ∀ t, t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1)
    (h : EdgeAdmissible F S w s c z') : z' ∈ P.image fun t => t.1 := by
  apply Finset.mem_image.mpr
  refine ⟨(z', edgeTargetLists F S s c), ?_, rfl⟩
  exact hP _ |>.2 (edgeAdmissible_target_valid_box F S w h)

private theorem logEdgePiece_sum {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (w : ArchRoot) (step : ℕ) (raw : Bool) (St Pr : Finset (Fin K))
    {ι : Type*} (R : Finset ι) (f : ι → LogPoint S.x K → ℂ)
    (P : Finset (EnvPoint S.x K))
    (hP : ∀ t, t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1)
    (σL : LogPoint S.x K) :
    logEdgePiece F S ρ w step raw St Pr (fun t => ∑ i ∈ R, f i t) σL =
      ∑ i ∈ R, logEdgePiece F S ρ w step raw St Pr (f i) σL := by
  classical
  let s := σL.1
  let good (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ) : Prop :=
    edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧ EdgeAdmissible F S w s c z'
  let out (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ) :
      LogPoint S.x K :=
    ((z', (edgeTargetLists F S s c, edgeNewMemory F S s c)),
      σL.2 ++ edgeBirths F S step s c)
  let coef (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ) : ℂ :=
    (((ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
        (∏ i : Fin K,
          match (c i).2 with
          | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
          | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
        ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S s c i) z') : ℝ) : ℂ) *
      edgeMultiplier F S (decide (step % 2 = 0)) raw s.2.1
        (edgeTargetLists F S s c) s.1 z')
  change
    (∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
      ∑' z' : ℤ × ℤ,
        if good c z' then coef c z' * (∑ i ∈ R, f i (out c z')) else 0) =
      ∑ i ∈ R,
        (∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
          ∑' z' : ℤ × ℤ,
            if good c z' then coef c z' * f i (out c z') else 0)
  have hpoint (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ) :
      (if good c z' then coef c z' * (∑ i ∈ R, f i (out c z')) else 0) =
        ∑ i ∈ R, if good c z' then coef c z' * f i (out c z') else 0 := by
    by_cases hg : good c z' <;> simp [hg, Finset.mul_sum]
  simp_rw [hpoint]
  calc
    _ = ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
          ∑ i ∈ R, ∑' z' : ℤ × ℤ,
            if good c z' then coef c z' * f i (out c z') else 0 := by
          apply Finset.sum_congr rfl
          intro c hc
          apply tsum_sum_finite_support (P.image fun t => t.1) R
          intro i z' hz'
          by_cases hg : good c z'
          · have hzmem := edgeAdmissible_position_mem F S w hP hg.2.2
            exact (hz' hzmem).elim
          · simp [hg]
    _ = _ := by rw [Finset.sum_comm]

private theorem logSym_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    {ι : Type*} (R : Finset ι) (f : ι → LogPoint S.x K → ℂ) :
    logSym F S (fun t => ∑ i ∈ R, f i t) =
      fun t => ∑ i ∈ R, logSym F S (f i) t := by
  classical
  funext σL
  unfold logSym
  calc
    ((permCount S.x K : ℂ))⁻¹ *
        ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          ∑ i ∈ R, f i ((σL.1.1, permuteLists σ σL.1.2.1, σL.1.2.2), σL.2) =
      ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
        ∑ i ∈ R, ((permCount S.x K : ℂ))⁻¹ *
          f i ((σL.1.1, permuteLists σ σL.1.2.1, σL.1.2.2), σL.2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro σ hσ
            rw [Finset.mul_sum]
    _ = ∑ i ∈ R, ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          ((permCount S.x K : ℂ))⁻¹ *
            f i ((σL.1.1, permuteLists σ σL.1.2.1, σL.1.2.2), σL.2) := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ R, ((permCount S.x K : ℂ))⁻¹ *
          ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            f i ((σL.1.1, permuteLists σ σL.1.2.1, σL.1.2.2), σL.2) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    _ = ∑ i ∈ R, logSym F S (f i) σL := rfl

private theorem logEdge_full_sum {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (w : ArchRoot) (step : ℕ) {ι : Type*} (R : Finset ι)
    (f : ι → LogPoint S.x K → ℂ) (P : Finset (EnvPoint S.x K))
    (hP : ∀ t, t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1) :
    logEdge F S ρ w EdgeKind.full step (fun t => ∑ i ∈ R, f i t) =
      fun t => ∑ i ∈ R, logEdge F S ρ w EdgeKind.full step (f i) t := by
  classical
  have hPiece (raw : Bool) (St Pr : Finset (Fin K)) (σL : LogPoint S.x K) :
      logEdgePiece F S ρ w step raw St Pr
          (logSym F S (fun t => ∑ i ∈ R, f i t)) σL =
        ∑ i ∈ R, logEdgePiece F S ρ w step raw St Pr (logSym F S (f i)) σL := by
    rw [logSym_sum]
    exact logEdgePiece_sum F S ρ w step raw St Pr R
      (fun i => logSym F S (f i)) P hP σL
  have hInner :
      (fun σL => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr
            (logSym F S (fun t => ∑ i ∈ R, f i t)) σL -
          logEdgePiece F S ρ w step false St Pr
            (logSym F S (fun t => ∑ i ∈ R, f i t)) σL)) =
      (fun σL => ∑ i ∈ R, ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr (logSym F S (f i)) σL -
          logEdgePiece F S ρ w step false St Pr (logSym F S (f i)) σL)) := by
    funext σL
    simp_rw [hPiece]
    simp_rw [← Finset.sum_sub_distrib]
    calc
      ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K), ∑ i ∈ R,
          (logEdgePiece F S ρ w step true St Pr (logSym F S (f i)) σL -
            logEdgePiece F S ρ w step false St Pr (logSym F S (f i)) σL) =
        ∑ St : Finset (Fin K), ∑ i ∈ R, ∑ Pr : Finset (Fin K),
          (logEdgePiece F S ρ w step true St Pr (logSym F S (f i)) σL -
            logEdgePiece F S ρ w step false St Pr (logSym F S (f i)) σL) := by
              apply Finset.sum_congr rfl
              intro St hSt
              rw [Finset.sum_comm]
      _ = ∑ i ∈ R, ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
          (logEdgePiece F S ρ w step true St Pr (logSym F S (f i)) σL -
            logEdgePiece F S ρ w step false St Pr (logSym F S (f i)) σL) := by
              rw [Finset.sum_comm]
  funext σL
  change logSym F S
      (fun t => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr
            (logSym F S (fun u => ∑ i ∈ R, f i u)) t -
          logEdgePiece F S ρ w step false St Pr
            (logSym F S (fun u => ∑ i ∈ R, f i u)) t)) σL = _
  rw [hInner, logSym_sum]
  rfl

private theorem envPoint_permute_mem {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (P : Finset (EnvPoint S.x K))
    (hP : ∀ t, t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1)
    (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) (t : EnvPoint S.x K)
    (ht : t ∈ P) : (t.1, permuteLists σ t.2) ∈ P := by
  apply (hP (t.1, permuteLists σ t.2)).mpr
  have h := (hP t).mp ht
  refine ⟨⟨h.1.1, validPrimeLists_permute σ t.2 h.1.2⟩, ?_⟩
  exact h.2

private theorem logSym_congr_on_P {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (P : Finset (EnvPoint S.x K))
    (hP : ∀ t, t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1)
    (f g : LogPoint S.x K → ℂ)
    (hfg : ∀ σL, (σL.1.1, σL.1.2.1) ∈ P → f σL = g σL)
    (σL : LogPoint S.x K) (hσ : (σL.1.1, σL.1.2.1) ∈ P) :
    logSym F S f σL = logSym F S g σL := by
  classical
  unfold logSym
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ'
  apply hfg
  exact envPoint_permute_mem F S w P hP σ (σL.1.1, σL.1.2.1) hσ

private theorem logEdgePiece_congr_on_P {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ) (raw : Bool) (St Pr : Finset (Fin K))
    (P : Finset (EnvPoint S.x K))
    (hP : ∀ t, t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1)
    (f g : LogPoint S.x K → ℂ)
    (hfg : ∀ σL, (σL.1.1, σL.1.2.1) ∈ P → f σL = g σL)
    (σL : LogPoint S.x K) :
    logEdgePiece F S ρ w step raw St Pr f σL =
      logEdgePiece F S ρ w step raw St Pr g σL := by
  classical
  let out (c : (i : Fin K) → EdgeChoice S.x F.a (σL.1.2.2 i) i) (z' : ℤ × ℤ) :
      LogPoint S.x K :=
    ((z', (edgeTargetLists F S σL.1 c, edgeNewMemory F S σL.1 c)),
      σL.2 ++ edgeBirths F S step σL.1 c)
  unfold logEdgePiece
  apply Finset.sum_congr rfl
  intro c hc
  apply tsum_congr
  intro z'
  by_cases hg : edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
      EdgeAdmissible F S w σL.1 c z'
  · simp only [if_pos hg]
    have hout : ((out c z').1.1, (out c z').1.2.1) ∈ P := by
      have htarget := (hP (z', edgeTargetLists F S σL.1 c)).mpr
        (edgeAdmissible_target_valid_box F S w hg.2.2)
      simpa [out] using htarget
    rw [hfg (out c z') hout]
  · simp [hg]

private theorem logEdge_full_congr_on_P {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ) (P : Finset (EnvPoint S.x K))
    (hP : ∀ t, t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1)
    (f g : LogPoint S.x K → ℂ)
    (hfg : ∀ σL, (σL.1.1, σL.1.2.1) ∈ P → f σL = g σL)
    (σL : LogPoint S.x K) (hσ : (σL.1.1, σL.1.2.1) ∈ P) :
    logEdge F S ρ w EdgeKind.full step f σL =
      logEdge F S ρ w EdgeKind.full step g σL := by
  classical
  have hSym : ∀ τ, (τ.1.1, τ.1.2.1) ∈ P →
      logSym F S f τ = logSym F S g τ := by
    intro τ hτ
    exact logSym_congr_on_P F S w P hP f g hfg τ hτ
  have hInside :
      (fun τ => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr (logSym F S f) τ -
          logEdgePiece F S ρ w step false St Pr (logSym F S f) τ)) =
      (fun τ => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr (logSym F S g) τ -
          logEdgePiece F S ρ w step false St Pr (logSym F S g) τ)) := by
    funext τ
    apply Finset.sum_congr rfl
    intro St hSt
    apply Finset.sum_congr rfl
    intro Pr hPr
    rw [logEdgePiece_congr_on_P F S ρ w step true St Pr P hP _ _ hSym τ,
      logEdgePiece_congr_on_P F S ρ w step false St Pr P hP _ _ hSym τ]
  change logSym F S (fun τ => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr (logSym F S f) τ -
          logEdgePiece F S ρ w step false St Pr (logSym F S f) τ)) σL =
      logSym F S (fun τ => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr (logSym F S g) τ -
          logEdgePiece F S ρ w step false St Pr (logSym F S g) τ)) σL
  exact congrArg (fun H : LogPoint S.x K → ℂ => logSym F S H σL) hInside

private theorem logSym_zero_of_badLog {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : LogPoint S.x K → ℂ)
    (hf : ∀ σL, ¬ (σL.2.map Prod.snd).Nodup → f σL = 0)
    (σL : LogPoint S.x K) (hbad : ¬ (σL.2.map Prod.snd).Nodup) :
    logSym F S f σL = 0 := by
  classical
  unfold logSym
  have hsum :
      (∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
        f ((σL.1.1, permuteLists σ σL.1.2.1, σL.1.2.2), σL.2)) = 0 := by
    apply Finset.sum_eq_zero
    intro σ hσ
    exact hf _ hbad
  simp [hsum]

private theorem bad_log_append_left {α : Type*} {l₁ l₂ : List α}
    (h : ¬ l₁.Nodup) : ¬ (l₁ ++ l₂).Nodup := by
  intro hn
  exact h (List.Nodup.of_append_left hn)

private theorem bad_log_append_right {α : Type*} {l₁ l₂ : List α}
    (h : ¬ l₂.Nodup) : ¬ (l₁ ++ l₂).Nodup := by
  intro hn
  exact h (List.Nodup.of_append_right hn)

private theorem tsum_zero_of_eq_zero {α : Type*} (f : α → ℂ)
    (h : ∀ a, f a = 0) : ∑' a, f a = 0 := by
  have hf : f = fun _ => 0 := funext h
  rw [hf]
  simp

private theorem logEdgePiece_zero_of_badLog {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ) (raw : Bool) (St Pr : Finset (Fin K))
    (f : LogPoint S.x K → ℂ)
    (hf : ∀ σL, ¬ (σL.2.map Prod.snd).Nodup → f σL = 0)
    (σL : LogPoint S.x K) (hbad : ¬ (σL.2.map Prod.snd).Nodup) :
    logEdgePiece F S ρ w step raw St Pr f σL = 0 := by
  classical
  unfold logEdgePiece
  apply Finset.sum_eq_zero
  intro c hc
  apply tsum_zero_of_eq_zero
  intro z'
  by_cases hg : edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
      EdgeAdmissible F S w σL.1 c z'
  · have hbadOut :
        ¬ ((σL.2 ++ edgeBirths F S step σL.1 c).map Prod.snd).Nodup := by
      simpa [List.map_append] using
        (bad_log_append_left hbad :
          ¬ (σL.2.map Prod.snd ++ (edgeBirths F S step σL.1 c).map Prod.snd).Nodup)
    let out : LogPoint S.x K :=
      ((z', (edgeTargetLists F S σL.1 c, edgeNewMemory F S σL.1 c)),
        σL.2 ++ edgeBirths F S step σL.1 c)
    have hfout : f out = 0 := hf out (by simpa [out] using hbadOut)
    simp [hg, out, hfout]
  · simp [hg]

private theorem logEdge_full_zero_of_badLog {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ)
    (f : LogPoint S.x K → ℂ)
    (hf : ∀ σL, ¬ (σL.2.map Prod.snd).Nodup → f σL = 0)
    (σL : LogPoint S.x K) (hbad : ¬ (σL.2.map Prod.snd).Nodup) :
    logEdge F S ρ w EdgeKind.full step f σL = 0 := by
  classical
  have hSym : ∀ τ, ¬ (τ.2.map Prod.snd).Nodup → logSym F S f τ = 0 :=
    fun τ hτ => logSym_zero_of_badLog F S f hf τ hτ
  have hInside : ∀ τ, ¬ (τ.2.map Prod.snd).Nodup →
      (∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr (logSym F S f) τ -
          logEdgePiece F S ρ w step false St Pr (logSym F S f) τ)) = 0 := by
    intro τ hτ
    apply Finset.sum_eq_zero
    intro St hSt
    apply Finset.sum_eq_zero
    intro Pr hPr
    rw [logEdgePiece_zero_of_badLog F S ρ w step true St Pr (logSym F S f)
          hSym τ hτ,
        logEdgePiece_zero_of_badLog F S ρ w step false St Pr (logSym F S f)
          hSym τ hτ]
    ring
  unfold logEdge
  simp only [EdgeKind.full]
  apply logSym_zero_of_badLog F S (fun τ =>
    ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
      (logEdgePiece F S ρ w step true St Pr (logSym F S f) τ -
        logEdgePiece F S ρ w step false St Pr (logSym F S f) τ)) hInside σL hbad

private theorem logGhost_zero_of_badLog {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) (f : LogPoint S.x K → ℂ)
    (hf : ∀ σL, ¬ (σL.2.map Prod.snd).Nodup → f σL = 0)
    (σL : LogPoint S.x K) (hbad : ¬ (σL.2.map Prod.snd).Nodup) :
    logGhost F S ρ j f σL = 0 := by
  classical
  unfold logGhost
  apply Finset.sum_eq_zero
  intro D hD
  apply tsum_zero_of_eq_zero
  intro l
  apply Finset.sum_eq_zero
  intro new hnew
  by_cases hDsub : ∀ i, D i ⊆ hitIndices (σL.1.2.2 i) σL.1.1
  · let batch : BirthLog K := (List.finRange K).flatMap (fun i =>
      List.ofFn fun k : Fin (l i) =>
        (BirthAddress.ghost j i k.val, ((new i k : ℕ))))
    have hbadAppend : ¬ (σL.2.map Prod.snd ++ batch.map Prod.snd).Nodup :=
      bad_log_append_left hbad
    have hbadOut : ¬ ((σL.2 ++ batch).map Prod.snd).Nodup := by
      simpa [List.map_append] using hbadAppend
    let out : LogPoint S.x K :=
      ((σL.1.1, σL.1.2.1, fun i =>
          removeIndices (σL.1.2.2 i) (D i) ++
            List.ofFn fun k : Fin (l i) => anchorAt (new i k) σL.1.1),
        σL.2 ++ batch)
    have hfout : f out = 0 := hf out (by simpa [out] using hbadOut)
    simp only [if_pos hDsub]
    change (((∏ i : Fin K, ghostGroupCoeff F S ρ j i
        (hitCount (σL.1.2.2 i) σL.1.1) (D i).card (l i)
        (List.ofFn fun k => (new i k : ℕ)) : ℝ) : ℂ) * f out) = 0
    rw [hfout]
    simp
  · simp [hDsub]

private theorem logHistoryFn_zero_of_badLog {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (γ : Option (EnvPath S.x K)) :
    ∀ k σL, ¬ (σL.2.map Prod.snd).Nodup →
      logHistoryFn F S ρ w none γ distinctWeight k σL = 0 := by
  intro k
  induction k with
  | zero =>
      intro σL hbad
      have hboundary : ∀ τ : LogPoint S.x K, ¬ (τ.2.map Prod.snd).Nodup →
          logBoundaryOut distinctWeight τ = 0 := by
        intro τ hτ
        simp [logBoundaryOut, distinctWeight, hτ]
      have hghost := logGhost_zero_of_badLog F S ρ (pathLength S.x)
        (logBoundaryOut distinctWeight) hboundary σL hbad
      have hghostTrunc :
          logGhost F S ρ (pathLength S.x)
            (logTrunc none (logBoundaryOut distinctWeight)) σL = 0 := by
        change logGhost F S ρ (pathLength S.x) (logBoundaryOut distinctWeight) σL = 0
        exact hghost
      cases γ with
      | none => simpa [logHistoryFn, logTrunc, logPathRestrict] using hghostTrunc
      | some path => simp [logHistoryFn, logTrunc, logPathRestrict, hghostTrunc]
  | succ k ih =>
      intro σL hbad
      have hEdge : ∀ τ, ¬ (τ.2.map Prod.snd).Nodup →
          logEdge F S ρ w EdgeKind.full (pathLength S.x - (k + 1))
            (logHistoryFn F S ρ w none γ distinctWeight k) τ = 0 := by
        intro τ hτ
        exact logEdge_full_zero_of_badLog F S ρ w (pathLength S.x - (k + 1))
          (logHistoryFn F S ρ w none γ distinctWeight k) (fun σ hσ => ih σ hσ) τ hτ
      have hghost := logGhost_zero_of_badLog F S ρ (pathLength S.x - (k + 1))
        (logEdge F S ρ w EdgeKind.full (pathLength S.x - (k + 1))
          (logHistoryFn F S ρ w none γ distinctWeight k)) hEdge σL hbad
      have hghostTrunc :
          logGhost F S ρ (pathLength S.x - (k + 1))
            (logTrunc none
              (logEdge F S ρ w EdgeKind.full (pathLength S.x - (k + 1))
                (logTrunc none (logHistoryFn F S ρ w none γ distinctWeight k)))) σL = 0 := by
        change logGhost F S ρ (pathLength S.x - (k + 1))
          (logEdge F S ρ w EdgeKind.full (pathLength S.x - (k + 1))
            (logHistoryFn F S ρ w none γ distinctWeight k)) σL = 0
        exact hghost
      cases γ with
      | none => simpa [logHistoryFn, logTrunc, logPathRestrict] using hghostTrunc
      | some path => simp [logHistoryFn, logTrunc, logPathRestrict, hghostTrunc]

private theorem logHistoryFn_congrPath {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (W : BirthLog K → ℂ) (k : ℕ)
    (γ γ' : EnvPath S.x K)
    (hγ : ∀ j, pathLength S.x - k ≤ j.val → γ j = γ' j) :
    logHistoryFn F S ρ w none (some γ) W k =
      logHistoryFn F S ρ w none (some γ') W k := by
  induction k with
  | zero =>
      have hlast : γ (Fin.last (pathLength S.x)) = γ' (Fin.last (pathLength S.x)) :=
        hγ _ (by simp)
      have hlast' : γ ⟨pathLength S.x, Nat.lt_succ_self _⟩ =
          γ' ⟨pathLength S.x, Nat.lt_succ_self _⟩ := by
        simpa [Fin.last] using hlast
      funext σL
      simp [logHistoryFn, logTrunc, logPathRestrict, hlast']
  | succ k ih =>
      let idx := historyRouteIndex (x := S.x) (k + 1)
      have hcur : γ idx = γ' idx := hγ idx (by simp [idx, historyRouteIndex])
      have hcur' : γ ⟨pathLength S.x - (k + 1), by omega⟩ =
          γ' ⟨pathLength S.x - (k + 1), by omega⟩ := by
        simpa [idx, historyRouteIndex] using hcur
      have htail : ∀ j, pathLength S.x - k ≤ j.val → γ j = γ' j := by
        intro j hj
        exact hγ j (by omega)
      have hrec := ih htail
      funext σL
      simp only [logHistoryFn, logTrunc]
      rw [hrec]
      simp [logPathRestrict, hcur']

private def historyGhostBatchLog {K : ℕ} (F : PDFix K) (S : PDScale) (j : ℕ)
    (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)) : BirthLog K :=
  (List.finRange K).flatMap fun i =>
    List.ofFn fun k : Fin (l i) => (BirthAddress.ghost j i k.val, (new i k : ℕ))

private theorem historyListFinRangeSum {n : ℕ} (g : Fin n → ℕ) :
    ((List.finRange n).map g).sum = ∑ i : Fin n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ]
      simp only [List.map_cons, List.map_map, Function.comp_def, List.sum_cons,
        Fin.sum_univ_succ]
      simpa using congrArg (fun z => g 0 + z) (ih fun i => g i.succ)

private theorem historyGhostBatch_values_mem {K : ℕ} (F : PDFix K) (S : PDScale)
    (j : ℕ) (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i))
    {p : ℕ} (hp : p ∈ (historyGhostBatchLog F S j l new).map Prod.snd) :
    p ∈ markedPrimes S.x K F.a := by
  classical
  simp only [historyGhostBatchLog, List.map_flatMap, List.mem_flatMap, List.mem_map] at hp
  rcases hp with ⟨i, hi, b, hb, hbp⟩
  rcases List.mem_ofFn.mp hb with ⟨k, hk⟩
  have hval : (new i k : ℕ) = p := by
    calc
      (new i k : ℕ) = (BirthAddress.ghost j i k.val, (new i k : ℕ)).2 := rfl
      _ = b.2 := congrArg Prod.snd hk
      _ = p := hbp
  have hval' : p = (new i k : ℕ) := hval.symm
  rw [hval']
  apply Finset.mem_biUnion.mpr
  exact ⟨i, Finset.mem_univ i, (new i k).property⟩

private theorem historyGhostBatch_values_length {K : ℕ} (F : PDFix K) (S : PDScale)
    (j : ℕ) (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)) :
    ((historyGhostBatchLog F S j l new).map Prod.snd).length = ∑ i : Fin K, l i := by
  classical
  simp only [historyGhostBatchLog, List.length_map, List.length_flatMap, List.length_ofFn]
  exact historyListFinRangeSum l

private theorem historyGhostBatch_not_nodup {K : ℕ} (F : PDFix K) (S : PDScale)
    (j : ℕ) (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i))
    (hl : (markedPrimes S.x K F.a).card < ∑ i : Fin K, l i) :
    ¬ ((historyGhostBatchLog F S j l new).map Prod.snd).Nodup := by
  intro hnd
  have hsubset :
      ((historyGhostBatchLog F S j l new).map Prod.snd).toFinset ⊆ markedPrimes S.x K F.a := by
    intro p hp
    exact historyGhostBatch_values_mem F S j l new (by simpa using hp)
  have hcard := List.toFinset_card_of_nodup hnd
  have hlen := historyGhostBatch_values_length F S j l new
  have hle :
      ((historyGhostBatchLog F S j l new).map Prod.snd).length ≤
        (markedPrimes S.x K F.a).card := by
    calc
      _ = ((historyGhostBatchLog F S j l new).map Prod.snd).toFinset.card := hcard.symm
      _ ≤ (markedPrimes S.x K F.a).card := Finset.card_mono hsubset
  omega

private theorem not_nodup_append_left {α : Type*} {l₁ l₂ : List α}
    (h : ¬ l₁.Nodup) : ¬ (l₁ ++ l₂).Nodup := by
  intro hn
  exact h (List.Nodup.of_append_left hn)

private theorem not_nodup_append_right {α : Type*} {l₁ l₂ : List α}
    (h : ¬ l₂.Nodup) : ¬ (l₁ ++ l₂).Nodup := by
  intro hn
  exact h (List.Nodup.of_append_right hn)

private theorem logGhost_sum_badLog {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) {ι : Type*} (R : Finset ι) (f : ι → LogPoint S.x K → ℂ)
    (hf : ∀ i σL, ¬ (σL.2.map Prod.snd).Nodup → f i σL = 0) :
    logGhost F S ρ j (fun σL => ∑ i ∈ R, f i σL) =
      fun σL => ∑ i ∈ R, logGhost F S ρ j (f i) σL := by
  classical
  funext σL
  let Q := (markedPrimes S.x K F.a).card
  let L : Finset (Fin K → ℕ) :=
    (Fintype.piFinset fun _ : Fin K => Finset.range (Q + 1)).filter
      (fun l => ∑ i : Fin K, l i ≤ Q)
  let good (D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length)) :=
    ∀ i, D i ⊆ hitIndices (σL.1.2.2 i) σL.1.1
  let out (D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length))
      (l : Fin K → ℕ) (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)) :
      LogPoint S.x K :=
    ((σL.1.1, σL.1.2.1, fun i => removeIndices (σL.1.2.2 i) (D i) ++
        List.ofFn fun k : Fin (l i) => anchorAt (new i k) σL.1.1),
      σL.2 ++ historyGhostBatchLog F S j l new)
  let coeff (D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length)
      ) (l : Fin K → ℕ) (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)) : ℂ :=
    ((∏ i : Fin K, ghostGroupCoeff F S ρ j i (hitCount (σL.1.2.2 i) σL.1.1)
        (D i).card (l i) (List.ofFn fun k => (new i k : ℕ)) : ℝ) : ℂ)
  let term (D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length)
      ) (l : Fin K → ℕ) (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i))
      (i : ι) : ℂ :=
    if good D then coeff D l new * f i (out D l new) else 0
  have hnotL (l : Fin K → ℕ) (hl : l ∉ L) :
      (markedPrimes S.x K F.a).card < ∑ i : Fin K, l i := by
    by_contra hn
    have hsum : ∑ i : Fin K, l i ≤ Q := by omega
    have hbound : ∀ i : Fin K, l i ≤ Q := by
      intro i
      have hle : l i ≤ ∑ j : Fin K, l j :=
        Finset.single_le_sum (s := Finset.univ) (f := l)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    have hpi : l ∈ Fintype.piFinset (fun _ : Fin K => Finset.range (Q + 1)) := by
      simp only [Fintype.mem_piFinset]
      intro i
      exact Finset.mem_range.mpr (by have := hbound i; omega)
    exact hl (Finset.mem_filter.mpr ⟨hpi, hsum⟩)
  have hbadTarget
      (D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length)
      ) (l : Fin K → ℕ)
      (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i))
      (hl : l ∉ L) : ¬ ((out D l new).2.map Prod.snd).Nodup := by
    have hbatch : ¬ ((historyGhostBatchLog F S j l new).map Prod.snd).Nodup :=
      historyGhostBatch_not_nodup F S j l new (by simpa [Q] using hnotL l hl)
    have happend :
        ¬ ((σL.2.map Prod.snd) ++ (historyGhostBatchLog F S j l new).map Prod.snd).Nodup :=
      bad_log_append_right hbatch
    simpa [out, List.map_append] using happend
  have hzero (D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length)
      ) (l : Fin K → ℕ) (hl : l ∉ L) (i : ι) :
      ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i), term D l new i = 0 := by
    apply Finset.sum_eq_zero
    intro new hnew
    by_cases hg : good D
    · simp only [term, if_pos hg]
      have hfout := hf i (out D l new) (hbadTarget D l new hl)
      simp [hfout]
    · simp [term, hg]
  have hterm (D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length)
      ) (l : Fin K → ℕ)
      (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)) :
      (if good D then coeff D l new * (∑ i ∈ R, f i (out D l new)) else 0) =
        ∑ i ∈ R, term D l new i := by
    by_cases hg : good D
    · simp [term, coeff, hg, Finset.mul_sum]
    · simp [term, hg]
  have hswapNew (D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length)
      ) (l : Fin K → ℕ) :
      (∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
        ∑ i ∈ R, term D l new i) =
      ∑ i ∈ R, ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
        term D l new i := by
    rw [Finset.sum_comm]
  have hswapL (D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length)) :
      (∑' l : Fin K → ℕ, ∑ i ∈ R,
        ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i), term D l new i) =
      ∑ i ∈ R, ∑' l : Fin K → ℕ,
        ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i), term D l new i :=
    tsum_sum_finite_support L R
      (fun l i => ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i), term D l new i)
      (by intro i l hl; exact hzero D l hl i)
  unfold logGhost
  change
    (∑ D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length),
      ∑' l : Fin K → ℕ, ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
        if good D then coeff D l new * (∑ i ∈ R, f i (out D l new)) else 0) =
    ∑ i ∈ R,
      ∑ D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length),
        ∑' l : Fin K → ℕ, ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
          term D l new i
  calc
    _ = ∑ D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length),
          ∑' l : Fin K → ℕ, ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
            ∑ i ∈ R, term D l new i := by
          apply Finset.sum_congr rfl
          intro D hD
          apply tsum_congr
          intro l
          apply Finset.sum_congr rfl
          intro new hnew
          exact hterm D l new
    _ = ∑ D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length),
          ∑' l : Fin K → ℕ, ∑ i ∈ R,
            ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i), term D l new i := by
          apply Finset.sum_congr rfl
          intro D hD
          apply tsum_congr
          intro l
          exact hswapNew D l
    _ = ∑ D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length),
          ∑ i ∈ R, ∑' l : Fin K → ℕ,
            ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i), term D l new i := by
          apply Finset.sum_congr rfl
          intro D hD
          exact hswapL D
    _ = ∑ i ∈ R,
          ∑ D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length),
            ∑' l : Fin K → ℕ,
              ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i), term D l new i := by
          rw [Finset.sum_comm]
    _ = _ := rfl

private theorem logGhost_congr_on_P {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) (P : Finset (EnvPoint S.x K))
    (f g : LogPoint S.x K → ℂ)
    (hfg : ∀ σL, (σL.1.1, σL.1.2.1) ∈ P → f σL = g σL)
    (σL : LogPoint S.x K) (hσ : (σL.1.1, σL.1.2.1) ∈ P) :
    logGhost F S ρ j f σL = logGhost F S ρ j g σL := by
  classical
  unfold logGhost
  apply Finset.sum_congr rfl
  intro D hD
  apply tsum_congr
  intro l
  apply Finset.sum_congr rfl
  intro new hnew
  by_cases hDsub : ∀ i, D i ⊆ hitIndices (σL.1.2.2 i) σL.1.1
  · simp only [if_pos hDsub]
    congr 1
    apply hfg
    exact hσ
  · simp [hDsub]

private theorem logHistoryFn_route_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (P : Finset (EnvPoint S.x K))
    (hP : ∀ t, t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1) (k : ℕ)
    (hk : k ≤ pathLength S.x) :
    ∀ σL : LogPoint S.x K, (σL.1.1, σL.1.2.1) ∈ P →
      logHistoryFn F S ρ w none none distinctWeight k σL =
        ∑ γ ∈ historyRouteFinset P k,
          logHistoryFn F S ρ w none (some γ) distinctWeight k σL := by
  induction k with
  | zero =>
      intro σL hσ
      let zσ := (σL.1.1, σL.1.2.1)
      let G := logGhost F S ρ (pathLength S.x)
        (logTrunc none (logBoundaryOut distinctWeight))
      have hbase (e : EnvPoint S.x K) :
          logHistoryFn F S ρ w none
              (some (Function.update historyDefaultPath (Fin.last (pathLength S.x)) e))
              distinctWeight 0 σL = if zσ = e then G σL else 0 := by
        have hlast :
            Function.update historyDefaultPath (Fin.last (pathLength S.x)) e
                ⟨pathLength S.x, Nat.lt_succ_self _⟩ = e := by
          have hidx :
              (⟨pathLength S.x, Nat.lt_succ_self _⟩ : Fin (pathLength S.x + 1)) =
                Fin.last (pathLength S.x) := by
            apply Fin.ext
            rfl
          rw [hidx]
          simp [Function.update]
        by_cases he : zσ = e
        · simp [logHistoryFn, logTrunc, logPathRestrict, zσ, G, he, hlast]
        · simp [logHistoryFn, logTrunc, logPathRestrict, zσ, G, he, hlast]
      rw [historyRouteFinset_zero_sum]
      simp_rw [hbase]
      change G σL = ∑ e ∈ P, if zσ = e then G σL else 0
      rw [Finset.sum_eq_single zσ]
      · simp
      · intro e he hne
        simp [Ne.symm hne]
      · intro hnot
        exact (hnot hσ).elim
  | succ k ih =>
      intro σL hkσ
      have hklt : k < pathLength S.x := by omega
      let idx := historyRouteIndex (x := S.x) (k + 1)
      let j := pathLength S.x - (k + 1)
      let zσ := (σL.1.1, σL.1.2.1)
      let routeK := historyRouteFinset P k
      let tailFn : LogPoint S.x K → ℂ := fun τ =>
        ∑ γ ∈ routeK, logHistoryFn F S ρ w none (some γ) distinctWeight k τ
      have hPvToP (τ : LogPoint S.x K)
          (hτ : (τ.1.1, τ.1.2.1) ∈ P) :
          logHistoryFn F S ρ w none none distinctWeight k τ = tailFn τ := by
        exact ih (by omega) τ hτ
      have hEdgeFun (τ : LogPoint S.x K)
          (hτ : (τ.1.1, τ.1.2.1) ∈ P) :
          logEdge F S ρ w EdgeKind.full j
              (logHistoryFn F S ρ w none none distinctWeight k) τ =
            logEdge F S ρ w EdgeKind.full j tailFn τ := by
        exact logEdge_full_congr_on_P F S ρ w j P hP
          (logHistoryFn F S ρ w none none distinctWeight k) tailFn hPvToP τ hτ
      have hbadEdge (γ : EnvPath S.x K) :
          ∀ τ, ¬ (τ.2.map Prod.snd).Nodup →
            logEdge F S ρ w EdgeKind.full j
              (logHistoryFn F S ρ w none (some γ) distinctWeight k) τ = 0 := by
        intro τ hbad
        exact logEdge_full_zero_of_badLog F S ρ w j
          (logHistoryFn F S ρ w none (some γ) distinctWeight k)
          (fun υ hυ => logHistoryFn_zero_of_badLog F S ρ w (some γ) k υ hυ) τ hbad
      have hleft :
          logHistoryFn F S ρ w none none distinctWeight (k + 1) σL =
            ∑ γ ∈ routeK,
              logGhost F S ρ j
                (logEdge F S ρ w EdgeKind.full j
                  (logHistoryFn F S ρ w none (some γ) distinctWeight k)) σL := by
        change logGhost F S ρ j
            (logEdge F S ρ w EdgeKind.full j
              (logHistoryFn F S ρ w none none distinctWeight k)) σL = _
        have hghostEdge := logGhost_congr_on_P F S ρ j P
          (logEdge F S ρ w EdgeKind.full j
            (logHistoryFn F S ρ w none none distinctWeight k))
          (logEdge F S ρ w EdgeKind.full j tailFn) hEdgeFun σL hkσ
        rw [hghostEdge]
        have hlin := logEdge_full_sum F S ρ w j routeK
          (fun γ => logHistoryFn F S ρ w none (some γ) distinctWeight k)
          P hP
        rw [hlin]
        exact congrFun (logGhost_sum_badLog F S ρ j routeK
          (fun γ => logEdge F S ρ w EdgeKind.full j
            (logHistoryFn F S ρ w none (some γ) distinctWeight k)) hbadEdge) σL
      have hfixed (γ : EnvPath S.x K) :
          (∑ e ∈ P,
            logHistoryFn F S ρ w none
              (some (Function.update γ idx e)) distinctWeight (k + 1) σL) =
            logGhost F S ρ j
              (logEdge F S ρ w EdgeKind.full j
                (logHistoryFn F S ρ w none (some γ) distinctWeight k)) σL := by
        have hselector (e : EnvPoint S.x K) :
            logHistoryFn F S ρ w none
                (some (Function.update γ idx e)) distinctWeight (k + 1) σL =
              if zσ = e then
                logGhost F S ρ j
                  (logEdge F S ρ w EdgeKind.full j
                    (logHistoryFn F S ρ w none (some γ) distinctWeight k)) σL
              else 0 := by
          have htail : ∀ t, pathLength S.x - k ≤ t.val →
              Function.update γ idx e t = γ t := by
            intro t ht
            by_cases hti : t = idx
            · subst t
              have hidx : idx.val < pathLength S.x - k := by
                simp [idx, historyRouteIndex]
                omega
              omega
            · simp [Function.update_of_ne hti]
          have hcongr := logHistoryFn_congrPath F S ρ w distinctWeight k
            (Function.update γ idx e) γ htail
          have hraw :
              logHistoryFn F S ρ w none
                  (some (Function.update γ idx e)) distinctWeight (k + 1) σL =
                if zσ = e then
                  logGhost F S ρ j
                    (logTrunc none
                      (logEdge F S ρ w EdgeKind.full j
                        (logTrunc none
                          (logHistoryFn F S ρ w none
                            (some (Function.update γ idx e)) distinctWeight k)))) σL
                else 0 := by
            simp [logHistoryFn, logTrunc, logPathRestrict, idx, historyRouteIndex,
              Function.update, zσ, j]
          calc
            _ = if zσ = e then
                  logGhost F S ρ j
                    (logTrunc none
                      (logEdge F S ρ w EdgeKind.full j
                        (logTrunc none
                          (logHistoryFn F S ρ w none
                            (some (Function.update γ idx e)) distinctWeight k)))) σL
                else 0 := hraw
            _ = if zσ = e then
                  logGhost F S ρ j
                    (logTrunc none
                      (logEdge F S ρ w EdgeKind.full j
                        (logTrunc none
                          (logHistoryFn F S ρ w none (some γ) distinctWeight k)))) σL
                else 0 := congrArg (fun H : LogPoint S.x K → ℂ =>
                  if zσ = e then
                    logGhost F S ρ j (logTrunc none
                      (logEdge F S ρ w EdgeKind.full j (logTrunc none H))) σL
                  else 0) hcongr
            _ = _ := rfl
        simp_rw [hselector]
        rw [Finset.sum_eq_single zσ]
        · simp
        · intro e he hne
          simp [Ne.symm hne]
        · intro hnot
          exact (hnot hkσ).elim
      rw [hleft]
      rw [historyRouteFinset_succ_sum P k hklt]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro γ hγ
      exact (hfixed γ).symm

private theorem initialLog_nodup_validLists {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (s : MemPoint x K) (hband : ∀ i j, s.2.1 i j ∈ primeBand x (a i))
    (hnd : ((initialLog s).map Prod.snd).Nodup) :
    ValidPrimeLists x K a s.2.1 := by
  have hflat :
      ((List.finRange K).flatMap fun i =>
        (List.finRange (slotCount x)).map fun j => s.2.1 i j).Nodup := by
    simpa [initialLog, List.map_flatMap, List.map_map, Function.comp_def] using hnd
  have hrows := (List.nodup_flatMap.mp hflat).1
  constructor
  · intro i j
    constructor
    · have hmem := hband i j
      unfold primeBand at hmem
      exact (Finset.mem_filter.mp hmem).2.1
    · exact hband i j
  · intro i j j' hne heq
    have hrow := hrows i (by simp)
    have hj : j ∈ List.finRange (slotCount x) := by simp
    have hj' : j' ∈ List.finRange (slotCount x) := by simp
    have heqidx := List.inj_on_of_nodup_map hrow hj hj' heq
    exact hne heqidx

private theorem logGhost_zero_function {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) :
    logGhost F S ρ j (fun _ => 0) = fun _ => 0 := by
  funext σL
  simp [logGhost]

private theorem logEdge_full_zero_function {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (j : ℕ) :
    logEdge F S ρ w EdgeKind.full j (fun _ => 0) = fun _ => 0 := by
  funext σL
  simp [logEdge, logSym, logEdgePiece]

private theorem logHistoryFn_zero_of_path_outside {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (P : Finset (EnvPoint S.x K))
    (hP : ∀ t, t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1) (k : ℕ)
    (hk : k ≤ pathLength S.x) :
    ∀ γ : EnvPath S.x K,
      (∃ t, pathLength S.x - k ≤ t.val ∧ γ t ∉ P) →
      ∀ σL, (σL.1.1, σL.1.2.1) ∈ P →
        logHistoryFn F S ρ w none (some γ) distinctWeight k σL = 0 := by
  induction k with
  | zero =>
      intro γ hbad σL hσ
      rcases hbad with ⟨t, ht, hnot⟩
      have htval : t.val = pathLength S.x := by omega
      have htEq : t = Fin.last (pathLength S.x) := by
        apply Fin.ext
        exact htval
      have hlast : γ (Fin.last (pathLength S.x)) ∉ P := by
        simpa [htEq] using hnot
      have hneq : (σL.1.1, σL.1.2.1) ≠ γ (Fin.last (pathLength S.x)) := by
        intro heq
        exact hlast (by simpa [heq] using hσ)
      have hlastIdx :
          (⟨pathLength S.x, Nat.lt_succ_self _⟩ : Fin (pathLength S.x + 1)) =
            Fin.last (pathLength S.x) := by
        apply Fin.ext
        rfl
      have hneq' : (σL.1.1, σL.1.2.1) ≠ γ
          ⟨pathLength S.x, Nat.lt_succ_self _⟩ := by
        simpa [hlastIdx] using hneq
      simp [logHistoryFn, logTrunc, logPathRestrict, hneq']
  | succ k ih =>
      intro γ hbad σL hσ
      have hklt : k < pathLength S.x := by omega
      let idx := historyRouteIndex (x := S.x) (k + 1)
      let j := pathLength S.x - (k + 1)
      have hIdxFin :
          (⟨j, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ : Fin (pathLength S.x + 1)) = idx := by
        apply Fin.ext
        simp [idx, j, historyRouteIndex]
      have hbad' := hbad
      rcases hbad' with ⟨t, ht, hnot⟩
      by_cases hcur : (σL.1.1, σL.1.2.1) = γ idx
      · have hcurP : γ idx ∈ P := by simpa [hcur] using hσ
        have hti : t ≠ idx := by
          intro heq
          subst t
          exact hnot hcurP
        have htTail : pathLength S.x - k ≤ t.val := by
          have hneVal : t.val ≠ idx.val := by
            intro heq
            apply hti
            exact Fin.ext heq
          change idx.val ≤ t.val at ht
          have hltVal : idx.val < t.val := lt_of_le_of_ne ht (Ne.symm hneVal)
          have hidxplus : idx.val + 1 = pathLength S.x - k := by
            simp [idx, historyRouteIndex]
            omega
          omega
        have hbadTail : ∃ t, pathLength S.x - k ≤ t.val ∧ γ t ∉ P :=
          ⟨t, htTail, hnot⟩
        have hrecZero (τ : LogPoint S.x K)
            (hτ : (τ.1.1, τ.1.2.1) ∈ P) :
            logHistoryFn F S ρ w none (some γ) distinctWeight k τ = 0 :=
          ih (by omega) γ hbadTail τ hτ
        have hEdgeZero (τ : LogPoint S.x K)
            (hτ : (τ.1.1, τ.1.2.1) ∈ P) :
            logEdge F S ρ w EdgeKind.full j
                (logHistoryFn F S ρ w none (some γ) distinctWeight k) τ = 0 := by
          rw [logEdge_full_congr_on_P F S ρ w j P hP
            (logHistoryFn F S ρ w none (some γ) distinctWeight k) (fun _ => 0)
            (fun υ hυ => hrecZero υ hυ) τ hτ]
          exact congrFun (logEdge_full_zero_function F S ρ w j) τ
        have hghostZero := logGhost_congr_on_P F S ρ j P
          (logEdge F S ρ w EdgeKind.full j
            (logHistoryFn F S ρ w none (some γ) distinctWeight k)) (fun _ => 0)
          hEdgeZero σL hσ
        have hfinal :
            logGhost F S ρ j
              (logEdge F S ρ w EdgeKind.full j
                (logHistoryFn F S ρ w none (some γ) distinctWeight k)) σL = 0 :=
          hghostZero.trans (congrFun (logGhost_zero_function F S ρ j) σL)
        have hfinalWrapped :
            logGhost F S ρ j
              (logTrunc none
                (logEdge F S ρ w EdgeKind.full j
                  (logTrunc none
                    (logHistoryFn F S ρ w none (some γ) distinctWeight k)))) σL = 0 := by
          change logGhost F S ρ j
              (logEdge F S ρ w EdgeKind.full j
                (logHistoryFn F S ρ w none (some γ) distinctWeight k)) σL = 0
          exact hfinal
        have hcurrent : (σL.1.1, σL.1.2.1) = γ
            ⟨j, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
          simpa [hIdxFin] using hcur
        simpa [logHistoryFn, logTrunc, logPathRestrict, j, hcurrent] using hfinalWrapped
      · have hcur' : (σL.1.1, σL.1.2.1) ≠ γ
            ⟨j, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
          simpa [hIdxFin] using hcur
        simp [logHistoryFn, logTrunc, logPathRestrict, j, hcur']

private noncomputable def historyInitialPrimeLists {x : ℝ} {K : ℕ}
    (a : Fin K → ℝ) : Finset (PrimeLists x K) :=
  Fintype.piFinset fun i : Fin K =>
    Fintype.piFinset fun j : Fin (slotCount x) => primeBand x (a i)

private noncomputable def historyInitialStates {x : ℝ} {K : ℕ}
    (a : Fin K → ℝ) : Finset (MemPoint x K) :=
  (historyInitialPrimeLists a).image fun p => ((1, 0), p, fun _ => [])

private noncomputable def historyInitialLogs {x : ℝ} {K : ℕ}
    (a : Fin K → ℝ) : Finset (LogPoint x K) :=
  (historyInitialStates a).image fun s => (s, initialLog s)

private theorem mem_historyInitialLogs {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (σL : LogPoint x K) :
    σL ∈ historyInitialLogs a ↔
      σL.1.1 = (1, 0) ∧ (∀ i, σL.1.2.2 i = []) ∧
        σL.2 = initialLog σL.1 ∧
        (∀ i j, σL.1.2.1 i j ∈ primeBand x (a i)) := by
  classical
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨s, hs, hσ⟩
    rcases Finset.mem_image.mp hs with ⟨p, hp, rfl⟩
    subst σL
    constructor
    · rfl
    constructor
    · intro i
      rfl
    constructor
    · rfl
    · simpa [historyInitialPrimeLists, Fintype.mem_piFinset] using hp
  · rintro ⟨hz, hmem, hlog, hband⟩
    apply Finset.mem_image.mpr
    refine ⟨σL.1, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨σL.1.2.1, ?_, ?_⟩
      · simpa [historyInitialPrimeLists, Fintype.mem_piFinset] using hband
      · exact Prod.ext hz.symm (Prod.ext rfl (funext hmem).symm)
    · exact Prod.ext rfl hlog.symm

private theorem logGhost_zero_of_boundary_pos_ne_e1 {K : ℕ} (F : PDFix K)
    (S : PDScale) (ρ : ℝ) (j : ℕ) (σL : LogPoint S.x K)
    (hpos : σL.1.1 ≠ (1, 0)) :
    logGhost F S ρ j (logBoundaryOut distinctWeight) σL = 0 := by
  classical
  unfold logGhost
  apply Finset.sum_eq_zero
  intro D hD
  apply tsum_zero_of_eq_zero
  intro l
  apply Finset.sum_eq_zero
  intro new hnew
  by_cases hDsub : ∀ i, D i ⊆ hitIndices (σL.1.2.2 i) σL.1.1
  · have hboundary :
        logBoundaryOut distinctWeight
          (((σL.1.1, σL.1.2.1, fun i =>
            removeIndices (σL.1.2.2 i) (D i) ++
              List.ofFn fun k : Fin (l i) => anchorAt (new i k) σL.1.1),
            σL.2 ++ (List.finRange K).flatMap fun i =>
              List.ofFn fun k : Fin (l i) =>
                (BirthAddress.ghost j i k.val, (new i k : ℕ)))) = 0 := by
      simp [logBoundaryOut, memBoundary, hpos]
    simp [hDsub, hboundary]
  · simp [hDsub]

private theorem logHistoryFn_zero_of_last_not_e1 {K : ℕ} (F : PDFix K)
    (S : PDScale) (ρ : ℝ) (w : ArchRoot) (γ : EnvPath S.x K) (k : ℕ)
    (hlast : (γ (Fin.last (pathLength S.x))).1 ≠ (1, 0)) :
    logHistoryFn F S ρ w none (some γ) distinctWeight k = fun _ => 0 := by
  induction k with
  | zero =>
      funext σL
      by_cases hmatch : (σL.1.1, σL.1.2.1) = γ (Fin.last (pathLength S.x))
      · have hpos : σL.1.1 ≠ (1, 0) := by
          intro hz
          apply hlast
          exact (congrArg Prod.fst hmatch).symm.trans hz
        have hghost := logGhost_zero_of_boundary_pos_ne_e1 F S ρ
          (pathLength S.x) σL hpos
        have hlastIdx :
            (⟨pathLength S.x, Nat.lt_succ_self _⟩ : Fin (pathLength S.x + 1)) =
              Fin.last (pathLength S.x) := by
          apply Fin.ext
          rfl
        have hmatch' : (σL.1.1, σL.1.2.1) =
            γ ⟨pathLength S.x, Nat.lt_succ_self _⟩ := by
          simpa [hlastIdx] using hmatch
        have hghostWrapped :
            logGhost F S ρ (pathLength S.x)
              (logTrunc none (logBoundaryOut distinctWeight)) σL = 0 := by
          change logGhost F S ρ (pathLength S.x)
            (logBoundaryOut distinctWeight) σL = 0
          exact hghost
        simpa [logHistoryFn, logTrunc, logPathRestrict, hmatch'] using hghostWrapped
      · have hlastIdx :
            (⟨pathLength S.x, Nat.lt_succ_self _⟩ : Fin (pathLength S.x + 1)) =
              Fin.last (pathLength S.x) := by
          apply Fin.ext
          rfl
        have hmatch' : (σL.1.1, σL.1.2.1) ≠
            γ ⟨pathLength S.x, Nat.lt_succ_self _⟩ := by
          simpa [hlastIdx] using hmatch
        simp [logHistoryFn, logTrunc, logPathRestrict, hmatch']
  | succ k ih =>
      funext σL
      have hrec := ih
      have hedge : logEdge F S ρ w EdgeKind.full
          (pathLength S.x - (k + 1))
          (logTrunc none (logHistoryFn F S ρ w none (some γ) distinctWeight k)) =
            (fun _ => 0) := by
        rw [hrec]
        exact logEdge_full_zero_function F S ρ w _
      have hghost : logGhost F S ρ (pathLength S.x - (k + 1))
          (logTrunc none
            (logEdge F S ρ w EdgeKind.full (pathLength S.x - (k + 1))
              (logTrunc none
                (logHistoryFn F S ρ w none (some γ) distinctWeight k)))) =
            (fun _ => 0) := by
        have hrec' : logHistoryFn F S ρ w none (some γ) distinctWeight k =
            (fun _ => 0) := hrec
        rw [hrec']
        change logGhost F S ρ (pathLength S.x - (k + 1))
          (logTrunc none
            (logEdge F S ρ w EdgeKind.full (pathLength S.x - (k + 1))
              (fun _ => 0))) = (fun _ => 0)
        rw [logEdge_full_zero_function]
        change logGhost F S ρ (pathLength S.x - (k + 1)) (fun _ => 0) = (fun _ => 0)
        exact logGhost_zero_function F S ρ _
      simp [logHistoryFn, logTrunc, logPathRestrict, hghost]

/-- `t2:pd.history-paths` (new node) — PD 04:234-246.  Exact decomposition of the distinct
history by the sequence of positions and active lists at the visits (ghosts do not move them;
the edges move along the path; distinct initial entries make every visit list valid). -/
theorem history_paths (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S →
          historyDistinct F S ρ w =
            ∑' γ : EnvPath S.x K,
              if IsEnvPathAdmissible F S γ then memHistory F S ρ w none (some γ) distinctWeight else 0 := by
  classical
  intro K F hF ρ hρ
  refine ⟨2, by norm_num, ?_⟩
  intro S hS hx0 w hw
  classical
  rcases hS with ⟨hxS, hHm, hHn, _, _, hY, hpad⟩
  have hxpos : 0 < S.x := by linarith
  have hpowpos : 0 < Real.rpow S.x δ := Real.rpow_pos_of_pos hxpos _
  have hHmpos : 0 < S.Hm := lt_of_lt_of_le hpowpos hHm
  have hHnpos : 0 < S.Hn := lt_of_lt_of_le hpowpos hHn
  have hYpos : 0 < S.Y := by
    unfold dyadicScales at hY
    rcases Finset.mem_filter.mp hY with ⟨himage, _⟩
    rcases Finset.mem_image.mp himage with ⟨n, _, hEq⟩
    rw [← hEq]
    positivity
  have hd0pos : 0 < (S.d₀ : ℝ) := by
    unfold padScales at hpad
    rcases Finset.mem_image.mp hpad with ⟨n, _, hEq⟩
    rw [← hEq]
    positivity
  have hUpos : 0 < S.U := by
    dsimp [PDScale.U, PDScale.H]
    exact mul_pos (mul_pos hd0pos hYpos) hHmpos
  have hVpos : 0 < S.V := by
    simpa [PDScale.V] using hHnpos
  have hlogpos : 0 < Real.log S.x := Real.log_pos (by linarith [hxS])
  let rArg := Real.rpow (Real.log S.x) (1 / 2 : ℝ) / 2
  have hrArg : 0 < rArg := by
    dsimp [rArg]
    exact div_pos (Real.rpow_pos_of_pos hlogpos _) (by norm_num)
  have hRpos : 0 < momentR S.x := by
    change 0 < ⌈rArg⌉₊
    by_contra hR
    have hRzero : (⌈rArg⌉₊ : ℕ) = 0 := by omega
    have hceil : rArg ≤ (⌈rArg⌉₊ : ℕ) := Nat.le_ceil rArg
    rw [hRzero] at hceil
    have hceil' : rArg ≤ 0 := by exact_mod_cast hceil
    exact (not_le_of_gt hrArg) hceil'
  have hNpos : 0 < pathLength S.x := by
    dsimp [pathLength]
    exact Nat.mul_pos (by omega) hRpos
  have hwRegion := hw
  rcases hw with ⟨hu1, hu2, hv1, hv2, _, _⟩
  have he1box : envBox S w (1, 0) := by
    simpa [envBox, ArchRoot.tau] using ⟨hu1, hu2, hv1, hv2⟩
  have hPfin := envPoint_valid_box_finite F S w hUpos hVpos hwRegion
  let P : Finset (EnvPoint S.x K) := hPfin.toFinset
  have hP (t : EnvPoint S.x K) :
      t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1 := by
    simp [P]
  let R : Finset (EnvPath S.x K) := historyRouteFinset P (pathLength S.x)
  let T : Finset (LogPoint S.x K) := historyInitialLogs F.a
  let coeff (σL : LogPoint S.x K) : ℂ :=
    (memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL)
  have hInitFacts (σL : LogPoint S.x K)
      (hμ : memMeasure F S σL.1 ≠ 0) (hb : logBoundaryIn σL ≠ 0) :
      σL ∈ T ∧ MemValid F S σL.1 ∧
        σL.1.1 = (1, 0) ∧ (∀ i, σL.1.2.2 i = []) ∧
        σL.2 = initialLog σL.1 := by
    have hlog : σL.2 = initialLog σL.1 := by
      by_contra hn
      apply hb
      simp [logBoundaryIn, hn]
    have hboundary : σL.1.1 = (1, 0) ∧ (∀ i, σL.1.2.2 i = []) := by
      by_contra hn
      apply hb
      simp [logBoundaryIn, hlog, memBoundary, hn]
    have hvalid : MemValid F S σL.1 := by
      by_contra hn
      apply hμ
      simp [memMeasure, hn]
    have hmemT : σL ∈ T := by
      apply (mem_historyInitialLogs F.a σL).2
      exact ⟨hboundary.1, hboundary.2, hlog, hvalid.2.1⟩
    exact ⟨hmemT, hvalid, hboundary.1, hboundary.2, hlog⟩
  have hcoeffzero : ∀ σL, σL ∉ T → coeff σL = 0 := by
    intro σL hσ
    by_cases hμ : memMeasure F S σL.1 = 0
    · simp [coeff, hμ]
    · by_cases hb : logBoundaryIn σL = 0
      · simp [coeff, hb]
      · exact (hσ (hInitFacts σL hμ hb).1).elim
  have hroutePoint (σL : LogPoint S.x K) :
      coeff σL * logHistoryFn F S ρ w none none distinctWeight (pathLength S.x) σL =
        ∑ γ ∈ R, coeff σL *
          logHistoryFn F S ρ w none (some γ) distinctWeight (pathLength S.x) σL := by
    by_cases hμ : memMeasure F S σL.1 = 0
    · simp [coeff, hμ]
    · by_cases hb : logBoundaryIn σL = 0
      · simp [coeff, hb]
      · obtain ⟨hT, hvalid, hz, hmem, hlog⟩ := hInitFacts σL hμ hb
        by_cases hnd : (σL.2.map Prod.snd).Nodup
        · have hndInit : ((initialLog σL.1).map Prod.snd).Nodup := by
            simpa [hlog] using hnd
          have hband : ∀ i j, σL.1.2.1 i j ∈ primeBand S.x (F.a i) := hvalid.2.1
          have hLists := initialLog_nodup_validLists F.a σL.1 hband hndInit
          have hEnv : EnvValid F S (σL.1.1, σL.1.2.1) := by
            refine ⟨?_, hLists⟩
            norm_num [hz, Int.gcd]
          have hsource : (σL.1.1, σL.1.2.1) ∈ P :=
            (hP _).2 ⟨hEnv, by simpa [hz] using he1box⟩
          have hroute := logHistoryFn_route_sum F S ρ w P hP
            (pathLength S.x) le_rfl σL hsource
          calc
            _ = coeff σL *
                (∑ γ ∈ R,
                  logHistoryFn F S ρ w none (some γ) distinctWeight
                    (pathLength S.x) σL) := congrArg (fun z => coeff σL * z) hroute
            _ = _ := by rw [Finset.mul_sum]
        · have hzeroNone :=
            logHistoryFn_zero_of_badLog F S ρ w none (pathLength S.x) σL hnd
          have hzeroPath (γ : EnvPath S.x K) :=
            logHistoryFn_zero_of_badLog F S ρ w (some γ) (pathLength S.x) σL hnd
          simp [hzeroNone, hzeroPath]
  have hfiniteDecomp :
      historyDistinct F S ρ w =
        ∑ γ ∈ R, memHistory F S ρ w none (some γ) distinctWeight := by
    unfold historyDistinct memHistory logInner
    change (∑' σL, coeff σL *
          logHistoryFn F S ρ w none none distinctWeight (pathLength S.x) σL) = _
    calc
      _ = ∑' σL, ∑ γ ∈ R, coeff σL *
            logHistoryFn F S ρ w none (some γ) distinctWeight (pathLength S.x) σL := by
          apply tsum_congr
          intro σL
          exact hroutePoint σL
      _ = ∑ γ ∈ R, ∑' σL, coeff σL *
            logHistoryFn F S ρ w none (some γ) distinctWeight (pathLength S.x) σL :=
          tsum_sum_finite_support T R
            (fun σL γ => coeff σL *
              logHistoryFn F S ρ w none (some γ) distinctWeight (pathLength S.x) σL)
            (by
              intro γ σL hσ
              simp [hcoeffzero σL hσ])
      _ = _ := rfl
  have hbadOutside (γ : EnvPath S.x K) (hγ : γ ∉ R) :
      ∃ t, pathLength S.x - pathLength S.x ≤ t.val ∧ γ t ∉ P := by
    by_contra hn
    have hall : ∀ t, γ t ∈ P := by
      intro t
      by_contra hnot
      exact hn ⟨t, by omega, hnot⟩
    have hroute : γ ∈ historyRouteFinset P (pathLength S.x) := by
      rw [mem_historyRouteFinset]
      constructor
      · intro t ht
        exact hall t
      · intro t ht
        have ht0 : t.val < 0 := by simpa using ht
        omega
    exact hγ (by simpa [R] using hroute)
  have hmemZeroOutside (γ : EnvPath S.x K) (hγ : γ ∉ R) :
      memHistory F S ρ w none (some γ) distinctWeight = 0 := by
    have hbad := hbadOutside γ hγ
    unfold memHistory logInner
    apply tsum_zero_of_eq_zero
    intro σL
    by_cases hT : σL ∈ T
    · rcases (mem_historyInitialLogs F.a σL).mp hT with ⟨hz, hmem, hlog, hband⟩
      by_cases hnd : (σL.2.map Prod.snd).Nodup
      · have hndInit : ((initialLog σL.1).map Prod.snd).Nodup := by
          simpa [hlog] using hnd
        have hLists := initialLog_nodup_validLists F.a σL.1 hband hndInit
        have hEnv : EnvValid F S (σL.1.1, σL.1.2.1) := by
          refine ⟨?_, hLists⟩
          norm_num [hz, Int.gcd]
        have hsource : (σL.1.1, σL.1.2.1) ∈ P :=
          (hP _).2 ⟨hEnv, by simpa [hz] using he1box⟩
        have hzero := logHistoryFn_zero_of_path_outside F S ρ w P hP
          (pathLength S.x) le_rfl γ hbad σL hsource
        change coeff σL *
          logHistoryFn F S ρ w none (some γ) distinctWeight (pathLength S.x) σL = 0
        rw [hzero]
        simp
      · have hzero :=
          logHistoryFn_zero_of_badLog F S ρ w (some γ) (pathLength S.x) σL hnd
        change coeff σL *
          logHistoryFn F S ρ w none (some γ) distinctWeight (pathLength S.x) σL = 0
        rw [hzero]
        simp
    · have hc :
          (memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL) = 0 := by
        simpa [coeff] using hcoeffzero σL hT
      change ((memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL)) *
        logHistoryFn F S ρ w none (some γ) distinctWeight (pathLength S.x) σL = 0
      rw [hc]
      simp
  have hrestrictedZeroNonAdm (γ : EnvPath S.x K) (hγ : γ ∈ R)
      (hAdm : ¬ IsEnvPathAdmissible F S γ) :
      memHistory F S ρ w none (some γ) distinctWeight = 0 := by
    have hroute := (mem_historyRouteFinset P (pathLength S.x) γ).mp
      (by simpa [R] using hγ)
    have hvalidAll : ∀ j, EnvValid F S (γ j) := by
      intro j
      have hj : pathLength S.x - pathLength S.x ≤ j.val := by omega
      exact (hP (γ j)).mp (hroute.1 j hj) |>.1
    have hfnzero (σL : LogPoint S.x K) (hT : σL ∈ T) :
        logHistoryFn F S ρ w none (some γ) distinctWeight (pathLength S.x) σL = 0 := by
      rcases (mem_historyInitialLogs F.a σL).mp hT with ⟨hz, _, _, _⟩
      by_cases hstart :
          (γ ⟨0, Nat.zero_lt_succ (pathLength S.x)⟩).1 = (1, 0)
      · by_cases hlast :
            (γ (Fin.last (pathLength S.x))).1 = (1, 0)
        · exact (hAdm ⟨hvalidAll, by simpa using hstart, hlast⟩).elim
        · exact congrFun (logHistoryFn_zero_of_last_not_e1 F S ρ w γ
            (pathLength S.x) hlast) σL
      · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hNpos.ne'
        rw [hn]
        have hcurrent : (σL.1.1, σL.1.2.1) ≠ γ ⟨0, by omega⟩ := by
          intro heq
          apply hstart
          exact (congrArg Prod.fst heq).symm.trans hz
        have hcurrent0 : (σL.1.1, σL.1.2.1) ≠ γ 0 := by
          simpa using hcurrent
        simp [logHistoryFn, logTrunc, logPathRestrict, hcurrent0, hn]
    unfold memHistory logInner
    apply tsum_zero_of_eq_zero
    intro σL
    by_cases hT : σL ∈ T
    · change coeff σL *
        logHistoryFn F S ρ w none (some γ) distinctWeight (pathLength S.x) σL = 0
      rw [hfnzero σL hT]
      simp
    · have hc :
          (memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL) = 0 := by
        simpa [coeff] using hcoeffzero σL hT
      change ((memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL)) *
        logHistoryFn F S ρ w none (some γ) distinctWeight (pathLength S.x) σL = 0
      rw [hc]
      simp
  have hsumAdm :
      (∑ γ ∈ R, memHistory F S ρ w none (some γ) distinctWeight) =
        ∑ γ ∈ R,
          if IsEnvPathAdmissible F S γ then
            memHistory F S ρ w none (some γ) distinctWeight else 0 := by
    apply Finset.sum_congr rfl
    intro γ hγ
    by_cases hAdm : IsEnvPathAdmissible F S γ
    · simp [hAdm]
    · simp [hAdm, hrestrictedZeroNonAdm γ hγ hAdm]
  have htsumAll :
      (∑' γ : EnvPath S.x K,
        if IsEnvPathAdmissible F S γ then
          memHistory F S ρ w none (some γ) distinctWeight else 0) =
        ∑ γ ∈ R,
          if IsEnvPathAdmissible F S γ then
            memHistory F S ρ w none (some γ) distinctWeight else 0 := by
    apply tsum_eq_sum
    intro γ hγ
    by_cases hAdm : IsEnvPathAdmissible F S γ
    · simp [hAdm, hmemZeroOutside γ hγ]
    · simp [hAdm]
  calc
    historyDistinct F S ρ w =
        ∑ γ ∈ R, memHistory F S ρ w none (some γ) distinctWeight := hfiniteDecomp
    _ = ∑ γ ∈ R,
          if IsEnvPathAdmissible F S γ then
            memHistory F S ρ w none (some γ) distinctWeight else 0 := hsumAdm
    _ = _ := htsumAll.symm

private theorem zmod_coords_not_both_zero (p : ℕ) (hp : p.Prime) (z : ℤ × ℤ)
    (hz : Int.gcd z.1 z.2 = 1) :
    (z.1 : ZMod p) ≠ 0 ∨ (z.2 : ZMod p) ≠ 0 := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  by_contra h
  push_neg at h
  have hdiv1 : (p : ℤ) ∣ z.1 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h.1
  have hdiv2 : (p : ℤ) ∣ z.2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h.2
  have hg : (p : ℤ) ∣ Int.gcd z.1 z.2 := dvd_gcd hdiv1 hdiv2
  have hzCast : ((Int.gcd z.1 z.2 : ℕ) : ℤ) = 1 := by exact_mod_cast hz
  have hdiv : (p : ℤ) ∣ 1 := by
    exact hzCast ▸ hg
  apply hp.not_dvd_one
  exact_mod_cast hdiv

private theorem projLine_eq_of_det_dvd (p : ℕ) (hp : p.Prime) (z z' : ℤ × ℤ)
    (hz : Int.gcd z.1 z.2 = 1) (hz' : Int.gcd z'.1 z'.2 = 1)
    (hdet : (p : ℤ) ∣ det2 z z') : projLine p z = projLine p z' := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hdetmod :
      (z.1 : ZMod p) * (z'.2 : ZMod p) -
        (z.2 : ZMod p) * (z'.1 : ZMod p) = 0 := by
    rcases hdet with ⟨n, hn⟩
    have hcast := congrArg (fun t : ℤ => (t : ZMod p)) hn
    simpa [det2] using hcast
  have hdetEq :
      (z.1 : ZMod p) * (z'.2 : ZMod p) =
        (z.2 : ZMod p) * (z'.1 : ZMod p) := sub_eq_zero.mp hdetmod
  by_cases hz2 : (z.2 : ZMod p) = 0
  · have hz1ne : (z.1 : ZMod p) ≠ 0 := by
      rcases zmod_coords_not_both_zero p hp z hz with h1 | h2
      · exact h1
      · exact (h2 hz2).elim
    have hz'2 : (z'.2 : ZMod p) = 0 := by
      have hprod : (z.1 : ZMod p) * (z'.2 : ZMod p) = 0 := by
        simpa [hz2] using hdetmod
      rcases mul_eq_zero.mp hprod with h1 | h2
      · exact (hz1ne h1).elim
      · exact h2
    simp [projLine, hz2, hz'2]
  · have hz2ne : (z.2 : ZMod p) ≠ 0 := hz2
    have hz'2ne : (z'.2 : ZMod p) ≠ 0 := by
      intro hzero
      have hprod : (z.2 : ZMod p) * (z'.1 : ZMod p) = 0 := by
        have h := hdetEq
        rw [hzero] at h
        simpa using h.symm
      rcases mul_eq_zero.mp hprod with h2 | h1
      · exact (hz2ne h2).elim
      · have hcoords := zmod_coords_not_both_zero p hp z' hz'
        rcases hcoords with hleft | hright
        · exact (hleft h1).elim
        · exact (hright hzero).elim
    have hratio :
        (z.1 : ZMod p) * (z.2 : ZMod p)⁻¹ =
          (z'.1 : ZMod p) * (z'.2 : ZMod p)⁻¹ := by
      calc
        (z.1 : ZMod p) * (z.2 : ZMod p)⁻¹ =
            ((z.1 : ZMod p) * (z'.2 : ZMod p)) *
              ((z.2 : ZMod p) * (z'.2 : ZMod p))⁻¹ := by
                field_simp [hz2ne, hz'2ne] <;> ring
        _ = ((z.2 : ZMod p) * (z'.1 : ZMod p)) *
              ((z.2 : ZMod p) * (z'.2 : ZMod p))⁻¹ := by rw [hdetEq]
        _ = (z'.1 : ZMod p) * (z'.2 : ZMod p)⁻¹ := by
                field_simp [hz2ne, hz'2ne] <;> ring
    simp [projLine, hz2, hz'2ne, hratio]

private theorem projLine_eq_of_transition_active {K : ℕ} (F : PDFix K)
    (S : PDScale) (z z' : ℤ × ℤ) (p q : PrimeLists S.x K)
    (hpv : ValidPrimeLists S.x K F.a p) (hqv : ValidPrimeLists S.x K F.a q)
    (hz : Int.gcd z.1 z.2 = 1) (hz' : Int.gcd z'.1 z'.2 = 1)
    (hslot : IsSlotTransition p q)
    (hpad : IsPadAdmissible S.d₀ (sharedProduct p) (det2 z z'))
    (r : ℕ) (hr : ∃ i j, p i j = r) (hr' : ∃ i j, q i j = r) :
    projLine r z = projLine r z' := by
  classical
  rcases hr with ⟨i, j, hsource⟩
  rcases hr' with ⟨i', j', htarget⟩
  have hrprime : r.Prime := by
    rw [← hsource]
    exact (hpv.1 i j).1
  have hj'lt : j'.val < momentJ S.x := by
    by_contra hn
    have hj'le : j'.val ≤ momentJ S.x := by
      have hlt := j'.isLt
      dsimp [slotCount] at hlt
      omega
    have hj'ge : momentJ S.x ≤ j'.val := Nat.le_of_not_gt hn
    have hj'val : j'.val = momentJ S.x := by omega
    have hj'eq : j' = lastSlot S.x := by
      apply Fin.ext
      simpa [lastSlot] using hj'val
    have hqLast : q i' (lastSlot S.x) = r := by simpa [hj'eq] using htarget
    have heq : q i' (lastSlot S.x) = p i j := hqLast.trans hsource.symm
    exact (hslot.2 i' i j) heq
  have hcopy : q i' j' = p i' j' := hslot.1 i' j' hj'lt
  have hshared : p i' j' = r := hcopy.symm.trans htarget
  have hdivNat : r ∣ sharedProduct p := by
    have hfactor : (if j'.val < momentJ S.x then p i' j' else 1) = r := by
      simp [hj'lt, hshared]
    have hinner : r ∣ ∏ j : Fin (slotCount S.x),
        if j.val < momentJ S.x then p i' j else 1 := by
      rw [← hfactor]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j')
    have houter :
        (∏ j : Fin (slotCount S.x),
          if j.val < momentJ S.x then p i' j else 1) ∣ sharedProduct p := by
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i')
    exact hinner.trans houter
  have hdivInt : (r : ℤ) ∣ (sharedProduct p : ℤ) := by exact_mod_cast hdivNat
  have hdet : (r : ℤ) ∣ det2 z z' := hdivInt.trans hpad.2.2
  exact projLine_eq_of_det_dvd r hrprime z z' hz hz' hdet

private theorem ordered_distinct_batch_sum (T : Finset ℕ) (ν : ℕ → ℝ) :
    (∑ new : Fin T.card → T,
      if Function.Bijective new then
        (∏ k, ν (new k).1) / (T.card.factorial : ℝ) else 0) =
      ∏ p ∈ T, ν p := by
  classical
  let n := T.card
  let B : Type := {f : Fin n → T // Function.Bijective f}
  let e0 : Fin n ≃ T := (Finset.equivFin T).symm
  let e : B ≃ Equiv.Perm (Fin n) :=
    { toFun := fun f => (Equiv.ofBijective f.1 f.2).trans e0.symm
      invFun := fun σ => ⟨σ.trans e0, (σ.trans e0).bijective⟩
      left_inv := by
        intro f
        apply Subtype.ext
        funext i
        simp [e0, Equiv.ofBijective]
      right_inv := by
        intro σ
        ext i
        simp [e0] }
  have hcard : Fintype.card B = n.factorial := by
    calc
      Fintype.card B = Fintype.card (Equiv.Perm (Fin n)) := Fintype.card_congr e
      _ = (Fintype.card (Fin n)).factorial := Fintype.card_perm
      _ = n.factorial := by simp [n]
  let Q : ℝ := ∏ p ∈ T, ν p
  have hprod (f : B) : (∏ k : Fin n, ν (f.1 k).1) = Q := by
    calc
      (∏ k : Fin n, ν (f.1 k).1) = ∏ t : T, ν t.1 :=
        Function.Bijective.prod_comp f.2 (fun t : T => ν t.1)
      _ = Q := by
        simpa [Q] using (Finset.prod_attach T ν)
  have hsumB :
      (∑ f : B, (∏ k : Fin n, ν (f.1 k).1) / (n.factorial : ℝ)) = Q := by
    calc
      _ = ∑ f : B, Q / (n.factorial : ℝ) := by
            apply Finset.sum_congr rfl
            intro f hf
            rw [hprod]
      _ = (Fintype.card B : ℝ) * (Q / (n.factorial : ℝ)) := by simp
      _ = Q := by rw [hcard]; field_simp
  change (∑ new : Fin n → T,
      if Function.Bijective new then
        (∏ k, ν (new k).1) / (n.factorial : ℝ) else 0) = Q
  calc
    _ = ∑ new ∈ (Finset.univ : Finset (Fin n → T)).filter Function.Bijective,
          (∏ k, ν (new k).1) / (n.factorial : ℝ) := by
          rw [Finset.sum_filter]
    _ = ∑ f : B, (∏ k, ν (f.1 k).1) / (n.factorial : ℝ) := by
          rw [← Finset.sum_subtype_eq_sum_filter]
          simp [B]
    _ = Q := hsumB

private theorem pathPrimeFactor_avg_eq_pathLifespan {K : ℕ} (F : PDFix K)
    (S : PDScale) (γ : EnvPath S.x K) (p : ℕ)
    (hbp0 : memoryBPrime S.x F.q_d p ≠ 0) :
    ((p : ℝ) + 1)⁻¹ *
        ∑ l : Fin (p + 1), pathPrimeFactor F S γ p l =
      memoryBPrime S.x F.q_d p * pathLifespan F S γ p := by
  have hbp : memoryBPrime S.x F.q_d p =
      1 - ∑ j : Fin (pathLength S.x + 1),
        memoryEta S.x F.q_d j.val / ((p : ℝ) + 1) := by
    unfold memoryBPrime
    congr 1
    rw [← Fin.sum_univ_eq_sum_range]
  simpa [pathPrimeFactor, pathLifespan, IsActiveAt, eq_comm] using
    (prime_lifespan p (pathLength S.x)
      (fun j => projLine p (γ j).1) (IsActiveAt γ p)
      (fun j => memoryEta S.x F.q_d j.val) (memoryBPrime S.x F.q_d p) hbp hbp0)

private theorem memoryPermutation_card {x : ℝ} {K : ℕ} (s : MemPoint x K) :
    Fintype.card (MemoryPermutation s) =
      ∏ i : Fin K, (s.2.2 i).length.factorial := by
  classical
  simp [MemoryPermutation, Fintype.card_perm]

private theorem memorySym_delta_eq_sum {x : ℝ} {K : ℕ} (s t : MemPoint x K) :
    memorySym (fun u => if u = t then (1 : ℂ) else 0) s =
      (Fintype.card (MemoryPermutation s) : ℂ)⁻¹ *
        ∑ σ : MemoryPermutation s,
          if memoryPermute s σ = t then (1 : ℂ) else 0 := by
  classical
  simp [memorySym]

private theorem memorySym_delta_row_le {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (T : Finset (MemPoint x K)) :
    (∑ t ∈ T, ‖memorySym (fun u => if u = t then (1 : ℂ) else 0) s‖) ≤ 1 := by
  classical
  let G := MemoryPermutation s
  let d := Fintype.card G
  have hG : Nonempty G := ⟨fun i => Equiv.refl _⟩
  have hdpos : 0 < d := by
    dsimp [d]
    exact Fintype.card_pos_iff.mpr hG
  have hdne : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdpos)
  have hnormInv : ‖(d : ℂ)⁻¹‖ = (d : ℝ)⁻¹ := by
    rw [norm_inv]
    simp [d]
  have hterm (t : MemPoint x K) :
      ‖memorySym (fun u => if u = t then (1 : ℂ) else 0) s‖ ≤
        (d : ℝ)⁻¹ * ∑ σ : G, if memoryPermute s σ = t then (1 : ℝ) else 0 := by
    unfold memorySym
    calc
      _ ≤ ‖(d : ℂ)⁻¹‖ *
            ∑ σ : G, ‖if memoryPermute s σ = t then (1 : ℂ) else 0‖ := by
          exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_left
              (norm_sum_le (Finset.univ : Finset G)
                (fun σ : G => if memoryPermute s σ = t then (1 : ℂ) else 0))
              (norm_nonneg _))
      _ = _ := by
        rw [hnormInv]
        congr 1
        apply Finset.sum_congr rfl
        intro σ hσ
        by_cases h : memoryPermute s σ = t <;> simp [h]
  have hinner (σ : G) :
      (∑ t ∈ T, if memoryPermute s σ = t then (1 : ℝ) else 0) ≤ 1 := by
    by_cases hσ : memoryPermute s σ ∈ T
    · rw [Finset.sum_eq_single (memoryPermute s σ)]
      · simp
      · intro t ht hne
        simp [Ne.symm hne]
      · intro hnot
        exact (hnot hσ).elim
    · have hzero :
          (∑ t ∈ T, if memoryPermute s σ = t then (1 : ℝ) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro t ht
        by_cases heq : memoryPermute s σ = t
        · subst t
          exact False.elim (hσ ht)
        · simp [heq]
      rw [hzero]
      norm_num
  calc
    _ ≤ ∑ t ∈ T, (d : ℝ)⁻¹ *
          ∑ σ : G, if memoryPermute s σ = t then (1 : ℝ) else 0 :=
        Finset.sum_le_sum fun t ht => hterm t
    _ = (d : ℝ)⁻¹ *
          ∑ σ : G, ∑ t ∈ T, if memoryPermute s σ = t then (1 : ℝ) else 0 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (d : ℝ)⁻¹ * ∑ σ : G, (1 : ℝ) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum fun σ hσ => hinner σ
        · positivity
    _ = 1 := by
      simp [d]

private theorem memSize_memoryPermute {x : ℝ} {K : ℕ} (s : MemPoint x K)
    (σ : MemoryPermutation s) : memSize (memoryPermute s σ) = memSize s := by
  simp [memSize, memoryPermute]

private theorem memorySym_delta_zero_of_memSize_ne {x : ℝ} {K : ℕ}
    (s t : MemPoint x K) (hsize : memSize s ≠ memSize t) :
    memorySym (fun u => if u = t then (1 : ℂ) else 0) s = 0 := by
  classical
  have hne (σ : MemoryPermutation s) : memoryPermute s σ ≠ t := by
    intro heq
    apply hsize
    calc
      memSize s = memSize (memoryPermute s σ) := (memSize_memoryPermute s σ).symm
      _ = memSize t := by rw [heq]
  simp [memorySym, hne]

private theorem removeIndices_length (l : List Particle)
    (D : Finset (Fin l.length)) : (removeIndices l D).length = l.length - D.card := by
  classical
  unfold removeIndices
  rw [List.length_filterMap_eq_countP]
  have hp :
      (fun a : Fin l.length => (if a ∈ D then none else some (l.get a)).isSome) =
        fun a => a ∉ D := by
    funext a
    by_cases h : a ∈ D <;> simp [h]
  rw [hp]
  have hfin : (List.finRange l.length).toFinset = (Finset.univ : Finset (Fin l.length)) := by
    ext a
    simp
  have hcount :
      (List.finRange l.length).countP (fun a => a ∉ D) =
        ((List.finRange l.length).toFinset.filter (fun a => a ∉ D)).card :=
    (List.nodup_finRange _).card_eq_countP.symm
  rw [hcount, hfin]
  have hfilter : (Finset.univ : Finset (Fin l.length)).filter (fun a => a ∉ D) =
      Finset.univ \ D := by
    ext a
    simp
  rw [hfilter, Finset.card_sdiff_of_subset (Finset.subset_univ D)]
  simp

private def selectIndices (l : List Particle) (D : Finset (Fin l.length)) : List Particle :=
  (List.finRange l.length).filterMap fun k => if k ∈ D then some (l.get k) else none

private theorem selectIndices_length (l : List Particle)
    (D : Finset (Fin l.length)) : (selectIndices l D).length = D.card := by
  classical
  unfold selectIndices
  rw [List.length_filterMap_eq_countP]
  have hp :
      (fun a : Fin l.length => (if a ∈ D then some (l.get a) else none).isSome) =
        fun a => a ∈ D := by
    funext a
    by_cases h : a ∈ D <;> simp [h]
  rw [hp]
  have hfin : (List.finRange l.length).toFinset = (Finset.univ : Finset (Fin l.length)) := by
    ext a
    simp
  have hcount :
      (List.finRange l.length).countP (fun a => a ∈ D) =
        ((List.finRange l.length).toFinset.filter (fun a => a ∈ D)).card :=
    (List.nodup_finRange _).card_eq_countP.symm
  rw [hcount, hfin]
  have hfilter : (Finset.univ : Finset (Fin l.length)).filter (fun a => a ∈ D) = D := by
    ext a
    simp
  rw [hfilter]

private def splitByMask {α : Type*} : List Bool → List α → List α × List α
  | [], _ => ([], [])
  | _ :: _, [] => ([], [])
  | true :: mask, a :: l =>
      let (kept, selected) := splitByMask mask l
      (kept, a :: selected)
  | false :: mask, a :: l =>
      let (kept, selected) := splitByMask mask l
      (a :: kept, selected)

private def weaveByMask {α : Type*} : List Bool → List α → List α → List α
  | [], kept, selected => kept ++ selected
  | true :: mask, kept, a :: selected => a :: weaveByMask mask kept selected
  | false :: mask, a :: kept, selected => a :: weaveByMask mask kept selected
  | _, _, _ => []

private theorem weave_splitByMask {α : Type*} (mask : List Bool) (l : List α)
    (hlen : mask.length = l.length) :
    weaveByMask mask (splitByMask mask l).1 (splitByMask mask l).2 = l := by
  induction mask generalizing l with
  | nil =>
      cases l with
      | nil => simp [weaveByMask, splitByMask]
      | cons a l => simp at hlen
  | cons b mask ih =>
      cases l with
      | nil => simp at hlen
      | cons a l =>
          have htail : mask.length = l.length := by simpa using hlen
          cases b <;>
            simp [splitByMask, weaveByMask, ih l htail]

private theorem splitByMask_eq_zip {α : Type*} (mask : List Bool) (l : List α)
    (hlen : mask.length = l.length) :
    splitByMask mask l =
      ((List.zip mask l).filterMap fun q => if q.1 then none else some q.2,
        (List.zip mask l).filterMap fun q => if q.1 then some q.2 else none) := by
  induction mask generalizing l with
  | nil =>
      cases l with
      | nil => simp [splitByMask]
      | cons a l => simp at hlen
  | cons b mask ih =>
      cases l with
      | nil => simp at hlen
      | cons a l =>
          have htail : mask.length = l.length := by simpa using hlen
          cases b <;> simp [splitByMask, ih l htail]

private def deletionMask (l : List Particle) (D : Finset (Fin l.length)) : List Bool :=
  (List.finRange l.length).map fun k => decide (k ∈ D)

private theorem filterMap_complement_perm {α β : Type*} (l : List α)
    (P : α → Prop) [DecidablePred P] (f : α → β) :
    List.Perm
      ((l.filterMap fun a => if P a then none else some (f a)) ++
        l.filterMap (fun a => if P a then some (f a) else none)) (l.map f) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases ha : P a
    · let A := l.filterMap (fun a => if P a then none else some (f a))
      let B := l.filterMap (fun a => if P a then some (f a) else none)
      have hmove : List.Perm (A ++ [f a] ++ B) ([f a] ++ A ++ B) := by
        exact List.Perm.append_right B
          (List.perm_append_comm (l₁ := A) (l₂ := [f a]))
      have hcons : ([f a] ++ A ++ B).Perm (f a :: List.map f l) := by
        simpa [A, B, List.append_assoc] using (List.Perm.cons (f a) ih)
      simpa [A, B, ha, List.append_assoc] using hmove.trans hcons
    · simp [ha, ih]

private theorem remove_select_perm (l : List Particle)
    (D : Finset (Fin l.length)) :
    List.Perm (removeIndices l D ++ selectIndices l D) l := by
  classical
  unfold removeIndices selectIndices
  simpa [List.map_get_finRange] using
    (filterMap_complement_perm (List.finRange l.length) (fun k => k ∈ D)
      (fun k => l.get k))

private theorem splitByMask_deletionMask (l : List Particle)
    (D : Finset (Fin l.length)) :
    splitByMask (deletionMask l D) l = (removeIndices l D, selectIndices l D) := by
  have hlen : (deletionMask l D).length = l.length := by simp [deletionMask]
  rw [splitByMask_eq_zip (deletionMask l D) l hlen]
  simp [deletionMask, removeIndices, selectIndices, List.map_get_finRange]

private theorem remove_select_prod_eq {β : Type*} [CommMonoid β]
    (l : List Particle) (D : Finset (Fin l.length)) (f : Particle → β) :
    ((removeIndices l D).map f).prod * ((selectIndices l D).map f).prod =
      (l.map f).prod := by
  have hperm := (remove_select_perm l D).map f
  have hprod := hperm.prod_eq
  simpa [List.map_append] using hprod

private theorem sum_powerset_binomial {α : Type*} [DecidableEq α]
    (H : Finset α) (a b : ℝ) :
    (∑ D ∈ H.powerset, a ^ D.card * b ^ (H.card - D.card)) = (a + b) ^ H.card := by
  classical
  calc
    _ = ∑ D ∈ H.powerset,
          (∏ _i ∈ D, a) * ∏ _i ∈ H \ D, b := by
          apply Finset.sum_congr rfl
          intro D hD
          have hsubset : D ⊆ H := Finset.mem_powerset.mp hD
          simp [Finset.prod_const, Finset.card_sdiff_of_subset hsubset]
    _ = ∏ i ∈ H, (a + b) := by
          symm
          exact Finset.prod_add (fun _ => a) (fun _ => b) H
    _ = (a + b) ^ H.card := by simp [Finset.prod_const]

private theorem sum_fin_function_prod {α : Type*} [Fintype α] [DecidableEq α]
    (n : ℕ) (w : α → ℝ) :
    (∑ g : Fin n → α, ∏ i : Fin n, w (g i)) = (∑ a : α, w a) ^ n := by
  classical
  rw [← Fintype.piFinset_univ]
  calc
    _ = ∏ i : Fin n, ∑ a : α, w a := by
      simpa using
        (Finset.prod_univ_sum (fun _ : Fin n => Finset.univ)
          (fun _ a => w a)).symm
    _ = _ := by simp [Finset.prod_const]

private theorem ghost_batch_sum_le_exp {α : Type*} [Fintype α] [DecidableEq α]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hνsum : (∑ a, ν a) ≤ 2)
    (c v : ℝ) (hc : 0 ≤ c) (hv : 0 ≤ v) :
    (∑' l : ℕ, ∑ f : Fin l → α,
      (c * v) ^ l / (l.factorial : ℝ) * ∏ k : Fin l, ν (f k)) ≤
        Real.exp (2 * c * v) := by
  classical
  let s : ℝ := ∑ a, ν a
  have hs : 0 ≤ s := Finset.sum_nonneg fun a ha => hν a
  have hsle : s ≤ 2 := hνsum
  have hinner (l : ℕ) :
      (∑ f : Fin l → α,
        (c * v) ^ l / (l.factorial : ℝ) * ∏ k : Fin l, ν (f k)) =
        ((c * v) * s) ^ l / (l.factorial : ℝ) := by
    calc
      _ = (c * v) ^ l / (l.factorial : ℝ) *
            ∑ f : Fin l → α, ∏ k : Fin l, ν (f k) := by rw [← Finset.mul_sum]
      _ = (c * v) ^ l / (l.factorial : ℝ) * s ^ l := by
            rw [sum_fin_function_prod]
      _ = ((c * v) * s) ^ l / (l.factorial : ℝ) := by
            calc
              _ = ((c * v) ^ l * s ^ l) / (l.factorial : ℝ) := by ring
              _ = ((c * v) * s) ^ l / (l.factorial : ℝ) := by rw [← mul_pow]
  have hseries :
      (∑' l : ℕ, ((c * v) * s) ^ l / (l.factorial : ℝ)) =
        Real.exp ((c * v) * s) := by
    rw [Real.exp_eq_exp_ℝ]
    exact (NormedSpace.expSeries_div_hasSum_exp ((c * v) * s)).tsum_eq
  have harg : (c * v) * s ≤ 2 * c * v := by
    calc
      (c * v) * s ≤ (c * v) * 2 := mul_le_mul_of_nonneg_left hsle
        (mul_nonneg hc hv)
      _ = 2 * c * v := by ring
  calc
    _ = ∑' l : ℕ, ((c * v) * s) ^ l / (l.factorial : ℝ) := by
      apply tsum_congr
      intro l
      exact hinner l
    _ = Real.exp ((c * v) * s) := hseries
    _ ≤ Real.exp (2 * c * v) := Real.exp_le_exp.mpr harg

private theorem ghost_scalar_cancellations (ρ q eta V : ℝ) (hρ : ρ ≠ 0) :
    ρ * (q / ρ ^ 2) * ρ = q ∧ (-eta * V / ρ) * ρ = -eta * V ∧
      (-eta / ρ) * ρ = -eta := by
  constructor
  · field_simp [hρ]
  constructor <;> field_simp [hρ]

/-- `t2:pd.history-path-value` (new node) — PD 04:234-274.  Along a fixed admissible path the
sum over memory choices with global birth distinctness factorizes over primes into lifespans:
store on leaving a nonfinal active run, promote on entering the next, ghost births/deletions at
the optional ghost endpoints; `ρ·(q_j/ρ²)·ρ = q_j` at pending hits; an active birth has measure
`ν_i(p) = ((p+1)b'_p)⁻¹V_i⁻¹`, a ghost birth `V_iν_i(p)` after cancellation, a promotion `V_i⁻¹`
(mem:run-charge); the symmetrization averages and `V_i⁻¹` weights are those of
`pathCoefficient`. -/
theorem history_path_value (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S → ∀ γ : EnvPath S.x K, IsEnvPathAdmissible F S γ →
          memHistory F S ρ w none (some γ) distinctWeight =
            pathCoefficient F S γ * (pathArch F S w γ : ℂ) *
              ((∏ p ∈ markedPrimes S.x K F.a, pathLifespan F S γ p : ℝ) : ℂ) := by
  sorry

/-- `t2:pd.memory-identity` — PD 04:43-274.  For every root of the region: the independent-line average of the
line-model moment equals the baseline `∏_p b'_p` times the distinct history value.  Proof:
`env_path_form`; the line average of a product over primes is the product of the per-prime
averages; `prime_lifespan`; `history_paths`; `history_path_value`. -/
private theorem memoryBPrime_pos_of_large_x {K : ℕ} (F : PDFix K) (hF : F.Valid) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ p ∈ markedPrimes x K F.a,
      0 < memoryBPrime x F.q_d p := by
  rcases hF with ⟨hBands, hqd, hqdlt, _, _, _⟩
  have hy : Filter.Tendsto (fun x : ℝ => Real.rpow (Real.log x) (1 / 10 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have hratio : Filter.Tendsto
      (fun x : ℝ => Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) /
        (Real.rpow (Real.log x) (1 / 10 : ℝ)) ^ (5 : ℝ)) atTop atTop :=
    (tendsto_exp_div_rpow_atTop 5).comp hy
  obtain ⟨xE, hxE⟩ := Filter.eventually_atTop.1
    ((Filter.tendsto_atTop.1 hratio) (3 : ℝ))
  obtain ⟨xY, hxY⟩ := Filter.eventually_atTop.1
    ((Filter.tendsto_atTop.1 hy) (2 : ℝ))
  let x₀ := max 2 (max xE (max xY (Real.exp 1)))
  have h₂ : 2 ≤ x₀ := by dsimp [x₀]; exact le_max_left _ _
  refine ⟨x₀, h₂, ?_⟩
  intro x hx p hp
  have hxE₀ : xE ≤ x₀ := by
    dsimp [x₀]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hxY₀ : xY ≤ x₀ := by
    dsimp [x₀]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hexp₀ : Real.exp 1 ≤ x₀ := by
    dsimp [x₀]
    exact le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hxE' : xE ≤ x := hxE₀.trans hx
  have hxY' : xY ≤ x := hxY₀.trans hx
  have hexp' : Real.exp 1 ≤ x := hexp₀.trans hx
  have hL : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hexp'
  let y := Real.rpow (Real.log x) (1 / 10 : ℝ)
  have hyx : 2 ≤ y := by simpa [y] using hxY x hxY'
  have hrx : 3 ≤ Real.exp y / y ^ (5 : ℝ) := by simpa [y] using hxE x hxE'
  rcases Finset.mem_biUnion.mp hp with ⟨i, _, hpi⟩
  have hband := (Finset.mem_filter.mp hpi).2.2.1
  have hai : (1 / 10 : ℝ) < F.a i := hBands.2.1 i |>.1
  have hlow : y ≤ Real.rpow (Real.log x) (F.a i) :=
    Real.rpow_le_rpow_of_exponent_le hL hai.le
  have hpLower : Real.exp y ≤ (p : ℝ) :=
    (Real.exp_le_exp.mpr hlow).trans hband
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hyx
  have hy5pos : 0 < y ^ (5 : ℝ) := Real.rpow_pos_of_pos hypos _
  have hExpLower : 3 * y ^ (5 : ℝ) ≤ Real.exp y :=
    (le_div_iff₀ hy5pos).mp hrx
  have hy5ge : (2 : ℝ) ≤ y ^ (5 : ℝ) := by
    calc
      2 ≤ y := hyx
      _ = Real.rpow y 1 := by simp
      _ ≤ Real.rpow y 5 :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [hyx]) (by norm_num)
  have hceil :
      (⌈Real.rpow (Real.log x) (1 / 2 : ℝ) / 2⌉₊ : ℝ) <
        Real.rpow (Real.log x) (1 / 2 : ℝ) / 2 + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (Real.rpow_nonneg (by linarith [hL]) _) (by norm_num))
  have hceil2 :
      (2 : ℝ) * (⌈Real.rpow (Real.log x) (1 / 2 : ℝ) / 2⌉₊ : ℝ) <
        Real.rpow (Real.log x) (1 / 2 : ℝ) + 2 := by
    have hmul := mul_lt_mul_of_pos_left hceil (by norm_num : (0 : ℝ) < 2)
    nlinarith
  have hN : (pathLength x : ℝ) < Real.rpow (Real.log x) (1 / 2 : ℝ) + 2 := by
    dsimp [pathLength, momentR]
    push_cast
    exact hceil2
  have hy5 : y ^ (5 : ℝ) = Real.rpow (Real.log x) (1 / 2 : ℝ) := by
    dsimp [y]
    rw [← Real.rpow_mul (by linarith [hL]) (1 / 10 : ℝ) (5 : ℝ)]
    norm_num
  have hpN : (pathLength x : ℝ) + 1 < (p : ℝ) := by
    rw [← hy5] at hN
    nlinarith [hExpLower, hpLower, hy5ge]
  have hpNat : pathLength x + 1 < p := by exact_mod_cast hpN
  have heta (j : ℕ) : memoryEta x F.q_d j ≤ 1 := by
    simp only [memoryEta, memoryQ]
    split_ifs <;> linarith [Real.sqrt_nonneg F.q_d]
  have hsum :
      (∑ j ∈ Finset.range (pathLength x + 1), memoryEta x F.q_d j) ≤
        (pathLength x + 1 : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (pathLength x + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => heta j
      _ = (pathLength x + 1 : ℝ) := by simp
  have hden : (pathLength x + 1 : ℝ) < (p : ℝ) + 1 := by
    exact_mod_cast lt_trans hpNat (Nat.lt_succ_self p)
  have hquot :
      (∑ j ∈ Finset.range (pathLength x + 1), memoryEta x F.q_d j) /
          ((p : ℝ) + 1) < 1 := by
    apply (div_lt_one₀ (by positivity)).2
    exact lt_of_le_of_lt hsum hden
  have hquot' :
      ∑ j ∈ Finset.range (pathLength x + 1),
          memoryEta x F.q_d j / ((p : ℝ) + 1) < 1 := by
    rw [← Finset.sum_div]
    exact hquot
  unfold memoryBPrime
  linarith

theorem memory_identity (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S →
          lineAverage (envMomentC F S w) =
            (memoryBaseline F S : ℂ) * historyDistinct F S ρ w := by
  classical
  intro K F hF ρ hρ
  obtain ⟨xE, hE, hEnvForm⟩ := env_path_form δ c₁ c₂ hδ hc₁ K F hF
  obtain ⟨xP, hP, hPaths⟩ := history_paths δ c₁ c₂ hδ hc₁ K F hF ρ hρ
  obtain ⟨xV, hV, hPathValue⟩ := history_path_value δ c₁ c₂ hδ hc₁ K F hF ρ hρ
  obtain ⟨xB, hB, hBPrimePos⟩ := memoryBPrime_pos_of_large_x F hF
  obtain ⟨Croot, xRoot, hCroot, hRoot, hRootBudget⟩ :=
    root_budget δ c₁ c₂ hδ hc₁ K F hF
  let x₀ := max xE (max xP (max xV (max xB xRoot)))
  have hx₀₂ : 2 ≤ x₀ := by
    dsimp [x₀]
    exact le_trans hE (le_max_left _ _)
  refine ⟨x₀, hx₀₂, ?_⟩
  intro S hS hx₀ w hw
  have hxE₀ : xE ≤ x₀ := by dsimp [x₀]; exact le_max_left _ _
  have hxP₀ : xP ≤ x₀ := by
    dsimp [x₀]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hxV₀ : xV ≤ x₀ := by
    dsimp [x₀]
    exact le_trans (le_max_left _ _) <| le_trans (le_max_right _ _) (le_max_right _ _)
  have hxB₀ : xB ≤ x₀ := by
    dsimp [x₀]
    exact le_trans (le_max_left _ _) <| le_trans (le_max_right _ _) <|
      le_trans (le_max_right _ _) (le_max_right _ _)
  have hxRoot₀ : xRoot ≤ x₀ := by
    dsimp [x₀]
    exact le_trans (le_max_right _ _) <| le_trans (le_max_right _ _) <|
      le_trans (le_max_right _ _) (le_max_right _ _)
  have hxE : xE ≤ S.x := hxE₀.trans hx₀
  have hxP : xP ≤ S.x := hxP₀.trans hx₀
  have hxV : xV ≤ S.x := hxV₀.trans hx₀
  have hxB : xB ≤ S.x := hxB₀.trans hx₀
  have hxRoot : xRoot ≤ S.x := hxRoot₀.trans hx₀
  have hEnv := hEnvForm S hS hxE w
  have hPathDecomp := hPaths S hS hxP w hw
  have hPathFact := hPathValue S hS hxV w hw
  have hBudget := hRootBudget S hS hxRoot
  let P := {p : ℕ // p ∈ markedPrimes S.x K F.a}
  letI : Fintype P :=
    Fintype.ofFinset (markedPrimes S.x K F.a) (by intro p; simp)
  have hAttach : (markedPrimes S.x K F.a).attach = (Finset.univ : Finset P) := by
    ext p
    simp [P]
  have hbpEq (p : P) :
      memoryBPrime S.x F.q_d p.1 =
        1 - ∑ j : Fin (pathLength S.x + 1),
          memoryEta S.x F.q_d j.val / ((p.1 : ℝ) + 1) := by
    unfold memoryBPrime
    congr 1
    rw [← Fin.sum_univ_eq_sum_range]
  have hbp0 (p : P) : memoryBPrime S.x F.q_d p.1 ≠ 0 :=
    ne_of_gt (hBPrimePos S.x hxB p.1 p.property)
  have hBaseCast :
      (memoryBaseline F S : ℂ) =
        ∏ p : P, (memoryBPrime S.x F.q_d p.1 : ℂ) := by
    have hR :
        (∏ p ∈ markedPrimes S.x K F.a, memoryBPrime S.x F.q_d p) =
          ∏ p : P, memoryBPrime S.x F.q_d p.1 := by
      exact Finset.prod_subtype _ (by intro p; rfl) (fun p => memoryBPrime S.x F.q_d p)
    simpa [memoryBaseline] using congrArg (fun r : ℝ => (r : ℂ)) hR
  have hLifeCast (γ : EnvPath S.x K) :
      ((∏ p ∈ markedPrimes S.x K F.a, pathLifespan F S γ p : ℝ) : ℂ) =
        ∏ p : P, (pathLifespan F S γ p.1 : ℂ) := by
    have hR :
        (∏ p ∈ markedPrimes S.x K F.a, pathLifespan F S γ p) =
          ∏ p : P, pathLifespan F S γ p.1 := by
      exact Finset.prod_subtype _ (by intro p; rfl) (fun p => pathLifespan F S γ p)
    simpa using congrArg (fun r : ℝ => (r : ℂ)) hR
  have hPrimeEq (γ : EnvPath S.x K) (p : P) :
      ((p.1 : ℂ) + 1)⁻¹ *
          ∑ l : Fin (p.1 + 1), (pathPrimeFactor F S γ p.1 l : ℂ) =
        (memoryBPrime S.x F.q_d p.1 : ℂ) * (pathLifespan F S γ p.1 : ℂ) := by
    have h := prime_lifespan p.1 (pathLength S.x)
      (fun j => projLine p.1 (γ j).1) (IsActiveAt γ p.1)
      (fun j => memoryEta S.x F.q_d j.val) (memoryBPrime S.x F.q_d p.1)
      (hbpEq p) (hbp0 p)
    have hc := congrArg (fun r : ℝ => (r : ℂ)) h
    simpa [pathPrimeFactor, pathLifespan, IsActiveAt, eq_comm] using hc
  have hPrimeProduct (γ : EnvPath S.x K) :
      ∏ p : P,
        (((p.1 : ℂ) + 1)⁻¹ *
          ∑ l : Fin (p.1 + 1), (pathPrimeFactor F S γ p.1 l : ℂ)) =
        (memoryBaseline F S : ℂ) *
          ((∏ p ∈ markedPrimes S.x K F.a, pathLifespan F S γ p : ℝ) : ℂ) := by
    calc
      _ = ∏ p : P,
            ((memoryBPrime S.x F.q_d p.1 : ℂ) *
              (pathLifespan F S γ p.1 : ℂ)) := by
            apply Finset.prod_congr rfl
            intro p hp
            exact hPrimeEq γ p
      _ = (∏ p : P, (memoryBPrime S.x F.q_d p.1 : ℂ)) *
            (∏ p : P, (pathLifespan F S γ p.1 : ℂ)) := by
            rw [Finset.prod_mul_distrib]
      _ = (memoryBaseline F S : ℂ) *
            ((∏ p ∈ markedPrimes S.x K F.a, pathLifespan F S γ p : ℝ) : ℂ) := by
            rw [← hBaseCast, ← hLifeCast]
  have hPi (γ : EnvPath S.x K) :
      (∑ ℓ : LineData S.x K F.a,
        ∏ p : P, (pathPrimeFactor F S γ p.1 (ℓ p) : ℂ)) =
        ∏ p : P, ∑ l : Fin (p.1 + 1), (pathPrimeFactor F S γ p.1 l : ℂ) := by
    rw [← Fintype.piFinset_univ]
    simpa using
      (Finset.prod_univ_sum (fun p : P => Finset.univ)
        (fun p l => (pathPrimeFactor F S γ p.1 l : ℂ))).symm
  let denom : ℂ :=
    ((∏ p ∈ markedPrimes S.x K F.a, ((p : ℝ) + 1) : ℝ) : ℂ)
  have hDenom : denom = ∏ p : P, ((p.1 : ℂ) + 1) := by
    have hR :
        (∏ p ∈ markedPrimes S.x K F.a, ((p : ℝ) + 1)) =
          ∏ p : P, ((p.1 : ℝ) + 1) := by
      exact (Finset.prod_attach (markedPrimes S.x K F.a)
        (fun p : ℕ => (p : ℝ) + 1)).symm
    simpa [denom] using congrArg (fun r : ℝ => (r : ℂ)) hR
  let lineProduct (γ : EnvPath S.x K) (ℓ : LineData S.x K F.a) : ℂ :=
    ((∏ p ∈ (markedPrimes S.x K F.a).attach,
      pathPrimeFactor F S γ p.1 (ℓ p) : ℝ) : ℂ)
  have hLineProduct (γ : EnvPath S.x K) (ℓ : LineData S.x K F.a) :
      lineProduct γ ℓ = ∏ p : P, (pathPrimeFactor F S γ p.1 (ℓ p) : ℂ) := by
    simp [lineProduct, hAttach] <;> rfl
  have hNormedPi (γ : EnvPath S.x K) :
      denom⁻¹ * (∑ ℓ : LineData S.x K F.a,
        lineProduct γ ℓ) =
        (memoryBaseline F S : ℂ) *
          ((∏ p ∈ markedPrimes S.x K F.a, pathLifespan F S γ p : ℝ) : ℂ) := by
    rw [hDenom]
    have hpi' :
        (∑ ℓ : LineData S.x K F.a, lineProduct γ ℓ) =
          ∏ p : P, ∑ l : Fin (p.1 + 1), (pathPrimeFactor F S γ p.1 l : ℂ) := by
      calc
        _ = ∑ ℓ : LineData S.x K F.a,
              ∏ p : P, (pathPrimeFactor F S γ p.1 (ℓ p) : ℂ) := by
              apply Finset.sum_congr rfl
              intro ℓ hℓ
              rw [hLineProduct]
        _ = _ := hPi γ
    rw [hpi']
    calc
      _ = (∏ p : P, (((p.1 : ℂ) + 1)⁻¹)) *
            (∏ p : P, ∑ l : Fin (p.1 + 1),
              (pathPrimeFactor F S γ p.1 l : ℂ)) := by
            rw [← Finset.prod_inv_distrib]
      _ = ∏ p : P,
            (((p.1 : ℂ) + 1)⁻¹ *
              ∑ l : Fin (p.1 + 1), (pathPrimeFactor F S γ p.1 l : ℂ)) := by
            rw [← Finset.prod_mul_distrib]
      _ = (memoryBaseline F S : ℂ) *
            ((∏ p ∈ markedPrimes S.x K F.a, pathLifespan F S γ p : ℝ) : ℂ) :=
            hPrimeProduct γ
  let lineTerm (γ : EnvPath S.x K) (ℓ : LineData S.x K F.a) : ℂ :=
    if IsEnvPathAdmissible F S γ then
      pathCoefficient F S γ * (pathArch F S w γ : ℂ) * lineProduct γ ℓ else 0
  let pathTerm (γ : EnvPath S.x K) : ℂ :=
    if IsEnvPathAdmissible F S γ then
      pathCoefficient F S γ * (pathArch F S w γ : ℂ) *
        ((∏ p ∈ markedPrimes S.x K F.a, pathLifespan F S γ p : ℝ) : ℂ) else 0
  let T : Finset (EnvPath S.x K) := hBudget.1.toFinset
  have hTmem (γ : EnvPath S.x K) :
      γ ∈ T ↔ IsContributingPath F S γ := by simp [T]
  have hlineTermZero (γ : EnvPath S.x K) (hγ : γ ∉ T)
      (ℓ : LineData S.x K F.a) : lineTerm γ ℓ = 0 := by
    have hnot : ¬ IsContributingPath F S γ := by
      intro hc
      exact hγ ((hTmem γ).2 hc)
    by_cases hadm : IsEnvPathAdmissible F S γ
    · by_cases hcoef : pathCoefficient F S γ = 0
      · simp [lineTerm, hadm, hcoef]
      · have harch : pathArch F S w γ = 0 := by
          by_contra harch
          exact hnot ⟨hadm, hcoef, w, hw, harch⟩
        simp [lineTerm, hadm, harch]
    · simp [lineTerm, hadm]
  have hpathTermZero (γ : EnvPath S.x K) (hγ : γ ∉ T) : pathTerm γ = 0 := by
    have hnot : ¬ IsContributingPath F S γ := by
      intro hc
      exact hγ ((hTmem γ).2 hc)
    by_cases hadm : IsEnvPathAdmissible F S γ
    · by_cases hcoef : pathCoefficient F S γ = 0
      · simp [pathTerm, hadm, hcoef]
      · have harch : pathArch F S w γ = 0 := by
          by_contra harch
          exact hnot ⟨hadm, hcoef, w, hw, harch⟩
        simp [pathTerm, hadm, harch]
    · simp [pathTerm, hadm]
  have htsumLine (ℓ : LineData S.x K F.a) :
      (∑' γ : EnvPath S.x K, lineTerm γ ℓ) = ∑ γ ∈ T, lineTerm γ ℓ := by
    apply tsum_eq_sum
    intro γ hγ
    exact hlineTermZero γ (by simpa [T] using hγ) ℓ
  have hsumLineTerm (γ : EnvPath S.x K) :
      (∑ ℓ : LineData S.x K F.a, lineTerm γ ℓ) =
        if IsEnvPathAdmissible F S γ then
          pathCoefficient F S γ * (pathArch F S w γ : ℂ) *
            (∑ ℓ : LineData S.x K F.a, lineProduct γ ℓ) else 0 := by
    by_cases hadm : IsEnvPathAdmissible F S γ
    · simp only [lineTerm, hadm, if_true]
      rw [← Finset.mul_sum]
    · simp [lineTerm, hadm]
  have hnormPathTerm (γ : EnvPath S.x K) :
      denom⁻¹ * (∑ ℓ : LineData S.x K F.a, lineTerm γ ℓ) =
        (memoryBaseline F S : ℂ) * pathTerm γ := by
    by_cases hadm : IsEnvPathAdmissible F S γ
    · rw [hsumLineTerm γ]
      simp only [if_pos hadm]
      calc
        denom⁻¹ *
            (pathCoefficient F S γ * (pathArch F S w γ : ℂ) *
              ∑ ℓ : LineData S.x K F.a, lineProduct γ ℓ) =
            pathCoefficient F S γ * (pathArch F S w γ : ℂ) *
              (denom⁻¹ * ∑ ℓ : LineData S.x K F.a, lineProduct γ ℓ) := by ring
        _ = pathCoefficient F S γ * (pathArch F S w γ : ℂ) *
              ((memoryBaseline F S : ℂ) *
                ((∏ p ∈ markedPrimes S.x K F.a, pathLifespan F S γ p : ℝ) : ℂ)) := by
              rw [hNormedPi γ]
        _ = (memoryBaseline F S : ℂ) * pathTerm γ := by
              simp only [pathTerm, if_pos hadm]
              ring
    · simp [hsumLineTerm γ, hadm, pathTerm]
  have hlineExpansion :
      lineAverage (envMomentC F S w) =
        (memoryBaseline F S : ℂ) * ∑ γ ∈ T, pathTerm γ := by
    unfold lineAverage
    calc
      _ = denom⁻¹ * ∑ ℓ : LineData S.x K F.a, ∑' γ : EnvPath S.x K, lineTerm γ ℓ := by
            congr 1
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            rw [hEnv ℓ]
            rfl
      _ = denom⁻¹ * ∑ ℓ : LineData S.x K F.a, ∑ γ ∈ T, lineTerm γ ℓ := by
            congr 1
            apply Finset.sum_congr rfl
            intro ℓ hℓ
            exact htsumLine ℓ
      _ = denom⁻¹ * ∑ γ ∈ T, ∑ ℓ : LineData S.x K F.a, lineTerm γ ℓ := by
            congr 1
            rw [Finset.sum_comm]
      _ = ∑ γ ∈ T,
            denom⁻¹ * ∑ ℓ : LineData S.x K F.a, lineTerm γ ℓ := by
            rw [Finset.mul_sum]
      _ = ∑ γ ∈ T, (memoryBaseline F S : ℂ) * pathTerm γ := by
            apply Finset.sum_congr rfl
            intro γ hγ
            exact hnormPathTerm γ
      _ = (memoryBaseline F S : ℂ) * ∑ γ ∈ T, pathTerm γ := by
            rw [← Finset.mul_sum]
  have hpathTsum : (∑' γ : EnvPath S.x K, pathTerm γ) = ∑ γ ∈ T, pathTerm γ := by
    apply tsum_eq_sum
    intro γ hγ
    exact hpathTermZero γ (by simpa [T] using hγ)
  have hhistoryPaths :
      (∑' γ : EnvPath S.x K, pathTerm γ) = historyDistinct F S ρ w := by
    rw [hPathDecomp]
    apply tsum_congr
    intro γ
    by_cases hadm : IsEnvPathAdmissible F S γ
    · simp [pathTerm, hadm, hPathFact γ hadm]
    · simp [pathTerm, hadm]
  rw [hlineExpansion, ← hpathTsum, hhistoryPaths]

/-- `t2:pd.truncation-adjoint` — PD 04:276-308.  REPLACES the frozen `truncation_adjoint`.
Inserting `Π_B`, `B = ⌈L²⌉`, around every operation changes the distinct history by
`O_A(L^{-AN})`: a history of memory size `> B` has `≥ B - KN` ghost births; with a factor `2` per
ghost birth the absolute ghost-only cost is `exp(O_K(N+1))`, the baseline and the path budget
`exp(O_K(L^{0.74}))`, so the omitted part is `2^{-B+KN} exp(O_K(L^{0.74}))`.  The adjoint rules
(mem:ghost-factorial), (mem:edge-factorial) of PD 04:310-363 are used in `ghost_edge_crude`
(column sums) and are not stated separately. -/
theorem truncation_adjoint (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ → ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S →
          ‖historyDistinct F S ρ w - historyDistinctTrunc F S ρ w‖ ≤
            C_A * Real.rpow S.L (-A * (S.N : ℝ)) := by
  sorry

private theorem memoryBPrime_half_of_large_x {K : ℕ} (F : PDFix K) (hF : F.Valid) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ p ∈ markedPrimes x K F.a,
      (1 / 2 : ℝ) ≤ memoryBPrime x F.q_d p := by
  rcases hF with ⟨hBands, hqd, hqdlt, _, _, _⟩
  have hy : Filter.Tendsto (fun x : ℝ => Real.rpow (Real.log x) (1 / 10 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have hratio : Filter.Tendsto
      (fun x : ℝ => Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) /
        (Real.rpow (Real.log x) (1 / 10 : ℝ)) ^ (5 : ℝ)) atTop atTop :=
    (tendsto_exp_div_rpow_atTop 5).comp hy
  obtain ⟨xE, hxE⟩ := Filter.eventually_atTop.1
    ((Filter.tendsto_atTop.1 hratio) (3 : ℝ))
  obtain ⟨xY, hxY⟩ := Filter.eventually_atTop.1
    ((Filter.tendsto_atTop.1 hy) (2 : ℝ))
  let x₀ := max 2 (max xE (max xY (Real.exp 1)))
  have h₂ : 2 ≤ x₀ := by dsimp [x₀]; exact le_max_left _ _
  refine ⟨x₀, h₂, ?_⟩
  intro x hx p hp
  have hxE₀ : xE ≤ x₀ := by
    dsimp [x₀]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hxY₀ : xY ≤ x₀ := by
    dsimp [x₀]
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hexp₀ : Real.exp 1 ≤ x₀ := by
    dsimp [x₀]
    exact le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hxE' : xE ≤ x := hxE₀.trans hx
  have hxY' : xY ≤ x := hxY₀.trans hx
  have hexp' : Real.exp 1 ≤ x := hexp₀.trans hx
  have hL : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hexp'
  let y := Real.rpow (Real.log x) (1 / 10 : ℝ)
  have hyx : 2 ≤ y := by simpa [y] using hxY x hxY'
  have hrx : 3 ≤ Real.exp y / y ^ (5 : ℝ) := by simpa [y] using hxE x hxE'
  rcases Finset.mem_biUnion.mp hp with ⟨i, _, hpi⟩
  have hband := (Finset.mem_filter.mp hpi).2.2.1
  have hai : (1 / 10 : ℝ) < F.a i := hBands.2.1 i |>.1
  have hlow : y ≤ Real.rpow (Real.log x) (F.a i) :=
    Real.rpow_le_rpow_of_exponent_le hL hai.le
  have hpLower : Real.exp y ≤ (p : ℝ) :=
    (Real.exp_le_exp.mpr hlow).trans hband
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num) hyx
  have hy5pos : 0 < y ^ (5 : ℝ) := Real.rpow_pos_of_pos hypos _
  have hExpLower : 3 * y ^ (5 : ℝ) ≤ Real.exp y :=
    (le_div_iff₀ hy5pos).mp hrx
  have hy5ge : (32 : ℝ) ≤ y ^ (5 : ℝ) := by
    calc
      32 = (2 : ℝ) ^ (5 : ℕ) := by norm_num
      _ ≤ y ^ (5 : ℕ) := by gcongr
      _ = y ^ (5 : ℝ) := (Real.rpow_natCast y 5).symm
  have hN : (pathLength x : ℝ) < y ^ (5 : ℝ) + 2 := by
    have hceil :
        (⌈Real.rpow (Real.log x) (1 / 2 : ℝ) / 2⌉₊ : ℝ) <
          Real.rpow (Real.log x) (1 / 2 : ℝ) / 2 + 1 :=
      Nat.ceil_lt_add_one (div_nonneg (Real.rpow_nonneg (by linarith [hL]) _) (by norm_num))
    have hceil2 :
        (2 : ℝ) * (⌈Real.rpow (Real.log x) (1 / 2 : ℝ) / 2⌉₊ : ℝ) <
          Real.rpow (Real.log x) (1 / 2 : ℝ) + 2 := by
      have hmul := mul_lt_mul_of_pos_left hceil (by norm_num : (0 : ℝ) < 2)
      nlinarith
    have hpath : (pathLength x : ℝ) < Real.rpow (Real.log x) (1 / 2 : ℝ) + 2 := by
      dsimp [pathLength, momentR]
      push_cast
      exact hceil2
    have hy5 : y ^ (5 : ℝ) = Real.rpow (Real.log x) (1 / 2 : ℝ) := by
      dsimp [y]
      rw [← Real.rpow_mul (by linarith [hL]) (1 / 10 : ℝ) (5 : ℝ)]
      norm_num
    simpa [hy5] using hpath
  have hpDouble : 2 * ((pathLength x + 1 : ℕ) : ℝ) < (p : ℝ) := by
    have hp3 : 3 * y ^ (5 : ℝ) ≤ (p : ℝ) := le_trans hExpLower hpLower
    have hNatCast : ((pathLength x + 1 : ℕ) : ℝ) = (pathLength x : ℝ) + 1 := by simp
    have hNplus : ((pathLength x + 1 : ℕ) : ℝ) < y ^ (5 : ℝ) + 3 := by
      rw [hNatCast]
      linarith [hN]
    have hpGap : 2 * (y ^ (5 : ℝ) + 3) ≤ 3 * y ^ (5 : ℝ) := by nlinarith [hy5ge]
    calc
      _ < 2 * (y ^ (5 : ℝ) + 3) := by nlinarith [hNplus]
      _ ≤ 3 * y ^ (5 : ℝ) := hpGap
      _ ≤ (p : ℝ) := hp3
  have heta (j : ℕ) : memoryEta x F.q_d j ≤ 1 := by
    simp only [memoryEta, memoryQ]
    split_ifs <;> linarith [Real.sqrt_nonneg F.q_d]
  have hsum :
      (∑ j ∈ Finset.range (pathLength x + 1), memoryEta x F.q_d j) ≤
        ((pathLength x + 1 : ℕ) : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (pathLength x + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => heta j
      _ = ((pathLength x + 1 : ℕ) : ℝ) := by simp
  have hpplus : 0 < (p : ℝ) + 1 := by positivity
  have hratio' : ((pathLength x + 1 : ℕ) : ℝ) / ((p : ℝ) + 1) < 1 / 2 := by
    apply (div_lt_iff₀ hpplus).2
    nlinarith [hpDouble]
  have hquot :
      (∑ j ∈ Finset.range (pathLength x + 1), memoryEta x F.q_d j) /
          ((p : ℝ) + 1) < 1 / 2 := by
    calc
      _ ≤ ((pathLength x + 1 : ℕ) : ℝ) / ((p : ℝ) + 1) :=
        div_le_div_of_nonneg_right hsum hpplus.le
      _ < 1 / 2 := hratio'
  unfold memoryBPrime
  rw [← Finset.sum_div]
  linarith

private theorem bandMass_le_two_log_two_of_large_x {K : ℕ} (F : PDFix K)
    (hF : F.Valid) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ i : Fin K,
      bandMass x (F.a i) ≤ 2 * Real.log 2 := by
  classical
  let x_i : Fin K → ℝ := fun i =>
    Classical.choose (band_mass (F.a i)
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 10) (hF.1.2.1 i).1)
      (lt_trans (hF.1.2.1 i).2 (by norm_num))
      (Real.log 2) (Real.log_pos (by norm_num)))
  have hx_i : ∀ i : Fin K,
      2 ≤ x_i i ∧ ∀ x : ℝ, x_i i ≤ x →
        |bandMass x (F.a i) - Real.log 2| ≤ Real.log 2 ∧
          0 < bandMass x (F.a i) := by
    intro i
    exact Classical.choose_spec (band_mass (F.a i)
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 10) (hF.1.2.1 i).1)
      (lt_trans (hF.1.2.1 i).2 (by norm_num))
      (Real.log 2) (Real.log_pos (by norm_num)))
  let x₀ : ℝ := 2 + ∑ i : Fin K, x_i i
  have hx₀ : 2 ≤ x₀ := by
    dsimp [x₀]
    have hsum : 0 ≤ ∑ i : Fin K, x_i i :=
      Finset.sum_nonneg fun i hi => by linarith [(hx_i i).1]
    linarith
  refine ⟨x₀, hx₀, ?_⟩
  intro x hx i
  have hsingle : x_i i ≤ ∑ j : Fin K, x_i j :=
    Finset.single_le_sum (s := Finset.univ) (f := x_i)
      (fun j hj => by linarith [(hx_i j).1]) (Finset.mem_univ i)
  have hxi : x_i i ≤ x₀ := by dsimp [x₀]; linarith
  have hmass := (hx_i i).2 x (le_trans hxi hx)
  have habs := (abs_le.mp hmass.1).2
  linarith

private theorem ghost_parenthesis_le_one {K : ℕ} (F : PDFix K) (hF : F.Valid)
    (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ) (v : ℝ)
    (hv : 2 / (ρ * (1 - Real.sqrt F.q_d / ρ ^ 2)) ≤ v) {x : ℝ} (j : ℕ) :
    memoryQ x F.q_d j / ρ ^ 2 + memoryEta x F.q_d j / (ρ * v) ≤ 1 := by
  rcases hF with ⟨_, hqd, hqdlt, _, _, _⟩
  rcases hρ with ⟨hρpos, hρlt, hroot⟩
  have hsquare : (Real.sqrt F.q_d) ^ 2 = F.q_d := Real.sq_sqrt hqd.le
  have hrootnonneg : 0 ≤ Real.sqrt F.q_d := Real.sqrt_nonneg _
  have hrootleOne : Real.sqrt F.q_d ≤ 1 := by
    by_contra h
    have hgt : 1 < Real.sqrt F.q_d := lt_of_not_ge h
    nlinarith [sq_nonneg (Real.sqrt F.q_d - 1), hsquare]
  have hrootle : F.q_d ≤ Real.sqrt F.q_d := by
    calc
      F.q_d = Real.sqrt F.q_d * Real.sqrt F.q_d := by nlinarith [hsquare]
      _ ≤ Real.sqrt F.q_d * 1 :=
        mul_le_mul_of_nonneg_left hrootleOne hrootnonneg
      _ = Real.sqrt F.q_d := by ring
  have hqjpos : 0 < memoryQ x F.q_d j := by
    unfold memoryQ
    split_ifs <;> positivity
  have hqj : memoryQ x F.q_d j ≤ Real.sqrt F.q_d := by
    unfold memoryQ
    split_ifs <;> linarith [hrootle]
  let g : ℝ := 1 - Real.sqrt F.q_d / ρ ^ 2
  have hg : 0 < g := by
    dsimp [g]
    apply sub_pos.mpr
    exact (div_lt_one (by positivity)).2 hroot
  have hdenρv : 0 < ρ * v := by
    have hvpos : 0 < 2 / (ρ * g) := div_pos (by norm_num) (mul_pos hρpos hg)
    exact mul_pos hρpos (lt_of_lt_of_le (div_pos (by norm_num) (mul_pos hρpos hg)) hv)
  have hlarge : 2 ≤ ρ * g * v := by
    have := (div_le_iff₀ (mul_pos hρpos hg)).mp hv
    nlinarith
  have hfrac : 1 / (ρ * v) ≤ g / 2 := by
    rw [div_le_iff₀ hdenρv]
    nlinarith [hlarge]
  have hqdiv : memoryQ x F.q_d j / ρ ^ 2 ≤ 1 - g := by
    calc
      _ ≤ Real.sqrt F.q_d / ρ ^ 2 :=
        div_le_div_of_nonneg_right hqj (sq_nonneg ρ)
      _ = 1 - g := by dsimp [g]; ring
  have heta : memoryEta x F.q_d j ≤ 1 := by
    unfold memoryEta
    linarith [hqjpos]
  have hetadiv : memoryEta x F.q_d j / (ρ * v) ≤ g / 2 := by
    calc
      _ ≤ 1 / (ρ * v) := div_le_div_of_nonneg_right heta hdenρv.le
      _ ≤ g / 2 := hfrac
  linarith

private theorem memoryNu_band_mass_le_two {K : ℕ} (F : PDFix K) {x : ℝ}
    (i : Fin K) (hV : 0 < bandMass x (F.a i))
    (hbp : ∀ p ∈ markedPrimes x K F.a,
      (1 / 2 : ℝ) ≤ memoryBPrime x F.q_d p)
    :
    ∑ p ∈ primeBand x (F.a i), memoryNu x K F.a F.q_d i p ≤ 2 := by
  classical
  have hV' : 0 < bandMass x (F.a i) := hV
  have hpx (p : ℕ) (hp : p ∈ primeBand x (F.a i)) : p ∈ markedPrimes x K F.a := by
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hp⟩
  have hterm (p : ℕ) (hp : p ∈ primeBand x (F.a i)) :
      memoryNu x K F.a F.q_d i p ≤ 2 / (bandMass x (F.a i) * (p : ℝ)) := by
    have hpPrime := (Finset.mem_filter.mp hp).2.1
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hpplus : (0 : ℝ) < (p : ℝ) + 1 := by positivity
    have hb := hbp p (hpx p hp)
    have hbpos : 0 < memoryBPrime x F.q_d p := lt_of_lt_of_le (by norm_num) hb
    have hden₁ : 0 < bandMass x (F.a i) * ((p : ℝ) + 1) * memoryBPrime x F.q_d p :=
      mul_pos (mul_pos hV' hpplus) hbpos
    have hden₂ : 0 < bandMass x (F.a i) * (p : ℝ) := mul_pos hV' hp0
    unfold memoryNu
    rw [div_le_div_iff₀ hden₁ hden₂]
    nlinarith
  calc
    _ ≤ ∑ p ∈ primeBand x (F.a i),
          2 / (bandMass x (F.a i) * (p : ℝ)) :=
        Finset.sum_le_sum fun p hp => hterm p hp
    _ = (2 / bandMass x (F.a i)) * bandMass x (F.a i) := by
        calc
          _ = ∑ p ∈ primeBand x (F.a i),
                (2 / bandMass x (F.a i)) * (1 / (p : ℝ)) := by
              apply Finset.sum_congr rfl
              intro p hp
              have hpPrime := (Finset.mem_filter.mp hp).2.1
              have hp0 : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
              field_simp [ne_of_gt hV', hp0.ne']
          _ = (2 / bandMass x (F.a i)) *
                ∑ p ∈ primeBand x (F.a i), 1 / (p : ℝ) := by
              rw [← Finset.mul_sum]
          _ = (2 / bandMass x (F.a i)) * bandMass x (F.a i) := by
              simp [bandMass]
    _ = 2 := by field_simp [ne_of_gt hV']

private theorem ghost_group_birth_sum_le_exp {K : ℕ} (F : PDFix K) (hF : F.Valid)
    {x : ℝ} (i : Fin K) (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ) (v : ℝ) (hv : 0 < v)
    (hV : 0 < bandMass x (F.a i))
    (hbp : ∀ p ∈ markedPrimes x K F.a,
      (1 / 2 : ℝ) ≤ memoryBPrime x F.q_d p) (j : ℕ) :
    (∑' l : ℕ, ∑ batch : Fin l → {p // p ∈ primeBand x (F.a i)},
      (memoryEta x F.q_d j * bandMass x (F.a i) / ρ * v) ^ l /
        (l.factorial : ℝ) * ∏ k : Fin l,
          memoryNu x K F.a F.q_d i (batch k).1) ≤
      Real.exp (2 * memoryEta x F.q_d j * bandMass x (F.a i) * v / ρ) := by
  classical
  rcases hF with ⟨_, hqd, hqdlt, _, _, _⟩
  rcases hρ with ⟨hρpos, hρlt, hroot⟩
  have hρsq : ρ ^ 2 < 1 := by nlinarith
  have hrootltone : Real.sqrt F.q_d < 1 := lt_trans hroot hρsq
  have hqjlt : memoryQ x F.q_d j < 1 := by
    unfold memoryQ
    split_ifs
    · exact hrootltone
    · exact hqdlt
  have heta : 0 ≤ memoryEta x F.q_d j := by
    unfold memoryEta
    linarith
  let P := primeBand x (F.a i)
  let α := {p // p ∈ P}
  letI : Fintype α := Fintype.ofFinset P (by intro p; simp [P])
  let ν : α → ℝ := fun p => memoryNu x K F.a F.q_d i p.1
  have hν : ∀ p : α, 0 ≤ ν p := by
    intro p
    have hpPrime := (Finset.mem_filter.mp p.2).2.1
    have hpplus : 0 < (p.1 : ℝ) + 1 := by positivity
    have hb : 0 < memoryBPrime x F.q_d p.1 :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
        (hbp p.1 (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, p.2⟩))
    have hden : 0 < bandMass x (F.a i) * ((p.1 : ℝ) + 1) *
        memoryBPrime x F.q_d p.1 := mul_pos (mul_pos hV hpplus) hb
    dsimp [ν]
    unfold memoryNu
    positivity
  have hνsum : (∑ p : α, ν p) ≤ 2 := by
    have hEq : (∑ p : α, ν p) =
        ∑ p ∈ P, memoryNu x K F.a F.q_d i p := by
      have hAttach : P.attach = (Finset.univ : Finset α) := by
        ext p
        simp [α, P]
      rw [← hAttach]
      exact Finset.sum_attach P (fun p => memoryNu x K F.a F.q_d i p)
    rw [hEq]
    exact memoryNu_band_mass_le_two F i hV hbp
  let c := memoryEta x F.q_d j * bandMass x (F.a i) / ρ
  have hc : 0 ≤ c := div_nonneg (mul_nonneg heta hV.le) hρpos.le
  have hsum := ghost_batch_sum_le_exp ν hν hνsum c v hc hv.le
  calc
    _ = ∑' l : ℕ, ∑ batch : Fin l → α,
          (c * v) ^ l / (l.factorial : ℝ) * ∏ k : Fin l, ν (batch k) := by
        apply tsum_congr
        intro l
        apply Finset.sum_congr rfl
        intro batch hbatch
        dsimp [c, ν]
    _ ≤ Real.exp (2 * c * v) := hsum
    _ = Real.exp (2 * memoryEta x F.q_d j * bandMass x (F.a i) * v / ρ) := by
        congr 1
        dsimp [c]
        ring

private theorem ghost_deletion_subset_sum_le_one {α : Type*} [DecidableEq α]
    (H : Finset α) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) :
    (∑ D ∈ H.powerset, a ^ D.card * b ^ (H.card - D.card)) ≤ 1 := by
  rw [sum_powerset_binomial]
  exact pow_le_one₀ (add_nonneg ha hb) hab

private theorem ghost_group_deletions_le_one {K : ℕ} (F : PDFix K) (hF : F.Valid)
    (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ) (v : ℝ) (hv0 : 0 < v)
    (hv : 2 / (ρ * (1 - Real.sqrt F.q_d / ρ ^ 2)) ≤ v)
    {x : ℝ} (j : ℕ) (l : List Particle) (z : ℤ × ℤ) :
    (∑ D ∈ (hitIndices l z).powerset,
      (memoryEta x F.q_d j / (ρ * v)) ^ D.card *
        (memoryQ x F.q_d j / ρ ^ 2) ^ ((hitIndices l z).card - D.card)) ≤ 1 := by
  have hqd : 0 < F.q_d := hF.2.1
  have hqdlt : F.q_d < 1 := hF.2.2.1
  have hρpos := hρ.1
  have hρlt := hρ.2.1
  have hroot := hρ.2.2
  have hη : 0 ≤ memoryEta x F.q_d j := by
    have hqj : memoryQ x F.q_d j < 1 := by
      have hρsq : ρ ^ 2 < 1 := by nlinarith [hρpos, hρlt]
      have hrootltone : Real.sqrt F.q_d < 1 := lt_trans hroot hρsq
      unfold memoryQ
      split_ifs <;> assumption
    unfold memoryEta
    linarith
  have hqnonneg : 0 ≤ memoryQ x F.q_d j := by
    unfold memoryQ
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact hF.2.1.le
  have ha : 0 ≤ memoryEta x F.q_d j / (ρ * v) :=
    div_nonneg hη (mul_nonneg hρpos.le hv0.le)
  have hb : 0 ≤ memoryQ x F.q_d j / ρ ^ 2 :=
    div_nonneg hqnonneg (sq_nonneg ρ)
  have hab : memoryEta x F.q_d j / (ρ * v) +
      memoryQ x F.q_d j / ρ ^ 2 ≤ 1 := by
    have h := ghost_parenthesis_le_one F hF ρ hρ v hv (x := x) j
    linarith
  exact ghost_deletion_subset_sum_le_one (hitIndices l z)
    (memoryEta x F.q_d j / (ρ * v)) (memoryQ x F.q_d j / ρ ^ 2) ha hb hab

private theorem ghost_group_choice_sum_le_exp {K : ℕ} (F : PDFix K) (hF : F.Valid)
    {x : ℝ} (i : Fin K) (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ) (v : ℝ) (hv : 0 < v)
    (hvlarge : 2 / (ρ * (1 - Real.sqrt F.q_d / ρ ^ 2)) ≤ v)
    (hV : 0 < bandMass x (F.a i))
    (hbp : ∀ p ∈ markedPrimes x K F.a,
      (1 / 2 : ℝ) ≤ memoryBPrime x F.q_d p)
    (j : ℕ) (l : List Particle) (z : ℤ × ℤ) :
    (∑ D ∈ (hitIndices l z).powerset,
      (memoryEta x F.q_d j / (ρ * v)) ^ D.card *
        (memoryQ x F.q_d j / ρ ^ 2) ^ ((hitIndices l z).card - D.card) *
        (∑' m : ℕ, ∑ batch : Fin m → {p // p ∈ primeBand x (F.a i)},
          (memoryEta x F.q_d j * bandMass x (F.a i) / ρ * v) ^ m /
            (m.factorial : ℝ) * ∏ k : Fin m,
              memoryNu x K F.a F.q_d i (batch k).1)) ≤
      Real.exp (2 * memoryEta x F.q_d j * bandMass x (F.a i) * v / ρ) := by
  let a := memoryEta x F.q_d j / (ρ * v)
  let b := memoryQ x F.q_d j / ρ ^ 2
  have hρpos := hρ.1
  have hD := ghost_group_deletions_le_one F hF ρ hρ v hv hvlarge (x := x) j l z
  have hBirth := ghost_group_birth_sum_le_exp F hF i ρ hρ v hv hV hbp j
  have hη : 0 ≤ memoryEta x F.q_d j := by
    have hqj : memoryQ x F.q_d j < 1 := by
      have hρsq : ρ ^ 2 < 1 := by nlinarith [hρ.1, hρ.2.1]
      have hrootltone : Real.sqrt F.q_d < 1 := lt_trans hρ.2.2 hρsq
      unfold memoryQ
      split_ifs <;> [exact hrootltone; exact hF.2.2.1]
    unfold memoryEta
    linarith
  have ha : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg hη (mul_nonneg hρpos.le hv.le)
  have hqnonneg : 0 ≤ memoryQ x F.q_d j := by
    unfold memoryQ
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact hF.2.1.le
  have hb : 0 ≤ b := by
    dsimp [b]
    exact div_nonneg hqnonneg (sq_nonneg ρ)
  have hweight (D : Finset (Fin l.length)) :
      0 ≤ a ^ D.card * b ^ ((hitIndices l z).card - D.card) :=
    mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _)
  have hExp : 0 < Real.exp (2 * memoryEta x F.q_d j * bandMass x (F.a i) * v / ρ) :=
    Real.exp_pos _
  calc
    _ ≤ ∑ D ∈ (hitIndices l z).powerset,
          a ^ D.card * b ^ ((hitIndices l z).card - D.card) *
            Real.exp (2 * memoryEta x F.q_d j * bandMass x (F.a i) * v / ρ) := by
        apply Finset.sum_le_sum
        intro D hD'
        exact mul_le_mul_of_nonneg_left hBirth (hweight D)
    _ = Real.exp (2 * memoryEta x F.q_d j * bandMass x (F.a i) * v / ρ) *
          ∑ D ∈ (hitIndices l z).powerset,
            a ^ D.card * b ^ ((hitIndices l z).card - D.card) := by
        rw [← Finset.sum_mul]
        ring
    _ ≤ Real.exp (2 * memoryEta x F.q_d j * bandMass x (F.a i) * v / ρ) * 1 :=
        mul_le_mul_of_nonneg_left hD hExp.le
    _ = Real.exp (2 * memoryEta x F.q_d j * bandMass x (F.a i) * v / ρ) := by ring

private theorem finite_pi_sum_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ι → Type*) [∀ i, Fintype (α i)]
    (f : ∀ i, α i → ℝ) :
    (∑ x : ∀ i, α i, ∏ i, f i (x i)) = ∏ i, ∑ a : α i, f i a := by
  classical
  rw [← Fintype.piFinset_univ]
  simpa using
    (Finset.prod_univ_sum (fun i => (Finset.univ : Finset (α i))) f).symm

private theorem sum_subtype_eq_sum_finset {α β : Type*} [DecidableEq α]
    [AddCommMonoid β] (T : Finset α) [Fintype {x // x ∈ T}] (f : α → β) :
    (∑ x : {x // x ∈ T}, f x.1) = ∑ x ∈ T, f x := by
  classical
  have hAttach : T.attach = (Finset.univ : Finset {x // x ∈ T}) := by
    ext x
    simp
  rw [← hAttach]
  exact Finset.sum_attach T f

private abbrev GhostDeletionChoice {x : ℝ} {K : ℕ}
    (s : MemPoint x K) (i : Fin K) :=
  {D : Finset (Fin (s.2.2 i).length) //
    D ∈ (hitIndices (s.2.2 i) s.1).powerset}

private noncomputable instance ghostDeletionChoiceFintype {x : ℝ} {K : ℕ}
    (s : MemPoint x K) (i : Fin K) : Fintype (GhostDeletionChoice s i) :=
  Fintype.ofFinite _

private abbrev GhostLengthChoice (B : ℕ) :=
  {m : ℕ // m ∈ Finset.range (B + 1)}

private noncomputable instance ghostLengthChoiceFintype (B : ℕ) :
    Fintype (GhostLengthChoice B) := Fintype.ofFinite _

private abbrev GhostPrimeChoice {x : ℝ} {K : ℕ}
    (F : PDFix K) (i : Fin K) :=
  {p // p ∈ primeBand x (F.a i)}

private abbrev GhostGroupChoice {x : ℝ} {K : ℕ}
    (F : PDFix K) (s : MemPoint x K) (B : ℕ) (i : Fin K) :=
  Σ D : GhostDeletionChoice s i,
    Σ m : GhostLengthChoice B, Fin m.1 → GhostPrimeChoice (x := x) F i

private def ghostOutputState {x : ℝ} {K : ℕ}
    (F : PDFix K) (s : MemPoint x K)
    (D : (i : Fin K) → Finset (Fin (s.2.2 i).length))
    (m : Fin K → ℕ)
    (new : (i : Fin K) → Fin (m i) → {p // p ∈ primeBand x (F.a i)}) :
    MemPoint x K :=
  (s.1, s.2.1, fun i =>
    removeIndices (s.2.2 i) (D i) ++
      List.ofFn fun k => anchorAt (new i k).1 s.1)

private theorem ghostOutputState_memSize {x : ℝ} {K : ℕ}
    (F : PDFix K) (s : MemPoint x K)
    (D : (i : Fin K) → Finset (Fin (s.2.2 i).length))
    (m : Fin K → ℕ)
    (new : (i : Fin K) → Fin (m i) → {p // p ∈ primeBand x (F.a i)}) :
    memSize (ghostOutputState F s D m new) =
      ∑ i : Fin K, ((s.2.2 i).length - (D i).card + m i) := by
  simp [memSize, ghostOutputState, removeIndices_length]

private theorem ghostOutputState_memSize_gt_of_large_batch {x : ℝ} {K : ℕ}
    (F : PDFix K) (s : MemPoint x K) (B : ℕ)
    (D : (i : Fin K) → Finset (Fin (s.2.2 i).length))
    (m : Fin K → ℕ)
    (new : (i : Fin K) → Fin (m i) → {p // p ∈ primeBand x (F.a i)})
    (hsize : memSize s ≤ B) (i : Fin K) (hm : 2 * B < m i) :
    B < memSize (ghostOutputState F s D m new) := by
  rw [ghostOutputState_memSize]
  have hlen : (s.2.2 i).length ≤ B := by
    have hle : (s.2.2 i).length ≤ memSize s := by
      unfold memSize
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun k : Fin K => (s.2.2 k).length)
        (by intro k hk; exact Nat.zero_le _) (Finset.mem_univ i)
    exact hle.trans hsize
  have hdel : (D i).card ≤ (s.2.2 i).length := by
    simpa using Finset.card_le_univ (D i)
  have hgroup : B < (s.2.2 i).length - (D i).card + m i := by omega
  have hsum :
      (s.2.2 i).length - (D i).card + m i ≤
        ∑ k : Fin K, ((s.2.2 k).length - (D k).card + m k) :=
    Finset.single_le_sum (s := Finset.univ)
      (f := fun k : Fin K => (s.2.2 k).length - (D k).card + m k)
      (by intro k hk; omega) (Finset.mem_univ i)
  exact hgroup.trans_le hsum

private def ghostKernelTerm {K : ℕ}
    (F : PDFix K) (S : PDScale) (s : MemPoint S.x K) (ρ : ℝ) (j : ℕ)
    (t : MemPoint S.x K)
    (D : (i : Fin K) → Finset (Fin (s.2.2 i).length))
    (m : Fin K → ℕ)
    (new : (i : Fin K) → Fin (m i) → {p // p ∈ primeBand S.x (F.a i)}) : ℂ :=
  if hD : ∀ i, D i ⊆ hitIndices (s.2.2 i) s.1 then
    ((∏ i : Fin K,
      ghostGroupCoeff F S ρ j i
        (hitCount (s.2.2 i) s.1) (D i).card (m i)
        (List.ofFn fun k => (new i k).1) : ℝ) : ℂ) *
      memorySym (fun u => if u = t then (1 : ℂ) else 0)
        (ghostOutputState F s D m new)
  else 0

private theorem ghostKernelTerm_zero_of_large_batch {K : ℕ}
    (F : PDFix K) (S : PDScale) (s t : MemPoint S.x K)
    (ρ : ℝ) (j B : ℕ)
    (hs : memSize s ≤ B) (ht : memSize t ≤ B)
    (D : (i : Fin K) → Finset (Fin (s.2.2 i).length)) (m : Fin K → ℕ)
    (new : (i : Fin K) → Fin (m i) → {p // p ∈ primeBand S.x (F.a i)})
    (i : Fin K) (hm : 2 * B < m i) :
    ghostKernelTerm F S s ρ j t D m new = 0 := by
  have hout := ghostOutputState_memSize_gt_of_large_batch F s B D m new hs i hm
  have hne : memSize (ghostOutputState F s D m new) ≠ memSize t := by omega
  by_cases hD : ∀ i, D i ⊆ hitIndices (s.2.2 i) s.1
  · simp [ghostKernelTerm, hD,
      memorySym_delta_zero_of_memSize_ne _ _ hne]
  · simp [ghostKernelTerm, hD]

private abbrev GhostBatchLengths (K B : ℕ) : Finset (Fin K → ℕ) :=
  Fintype.piFinset fun _ : Fin K => Finset.range (2 * B + 1)

private theorem ghostKernelTerm_zero_of_length_vec_notin {K : ℕ}
    (F : PDFix K) (S : PDScale) (s t : MemPoint S.x K)
    (ρ : ℝ) (j B : ℕ) (hs : memSize s ≤ B) (ht : memSize t ≤ B)
    (D : (i : Fin K) → Finset (Fin (s.2.2 i).length)) (m : Fin K → ℕ)
    (new : (i : Fin K) → Fin (m i) → {p // p ∈ primeBand S.x (F.a i)})
    (hm : m ∉ GhostBatchLengths K B) : ghostKernelTerm F S s ρ j t D m new = 0 := by
  have hnotL : ¬ ∀ i : Fin K, m i ∈ Finset.range (2 * B + 1) := by
    simpa [GhostBatchLengths, Fintype.mem_piFinset] using hm
  have hnot : ¬ ∀ i : Fin K, m i ≤ 2 * B := by
    intro hall
    apply hnotL
    intro i
    have hmi : m i ≤ 2 * B := hall i
    exact Finset.mem_range.mpr (by omega)
  rcases not_forall.mp hnot with ⟨i, hi⟩
  have hmi : 2 * B < m i := by omega
  exact ghostKernelTerm_zero_of_large_batch F S s t ρ j B hs ht D m new i hmi

private def ghostChoiceKernelTerm {K : ℕ}
    (F : PDFix K) (S : PDScale) (s t : MemPoint S.x K) (ρ : ℝ) (j B : ℕ)
    (choices : (i : Fin K) → GhostGroupChoice F s (2 * B) i) : ℂ :=
  ghostKernelTerm F S s ρ j t
    (fun i => (choices i).1.1)
    (fun i => (choices i).2.1.1)
    (fun i k => (choices i).2.2 k)

private def ghostChoiceCoeffReal {K : ℕ}
    (F : PDFix K) (S : PDScale) (s : MemPoint S.x K) (ρ : ℝ) (j B : ℕ)
    (choices : (i : Fin K) → GhostGroupChoice F s B i) : ℝ :=
  ∏ i : Fin K,
    ghostGroupCoeff F S ρ j i (hitCount (s.2.2 i) s.1)
      (choices i).1.1.card (choices i).2.1.1
      (List.ofFn fun k => ((choices i).2.2 k).1)

private theorem ghostChoiceKernelTerm_row_sum_le {K : ℕ}
    (F : PDFix K) (S : PDScale) (s : MemPoint S.x K) (ρ : ℝ) (j B : ℕ)
    (choices : (i : Fin K) → GhostGroupChoice F s (2 * B) i) (v : ℝ) (hv : 0 < v)
    (T : Finset (MemPoint S.x K)) :
    (∑ t ∈ T,
      ‖ghostChoiceKernelTerm F S s t ρ j B choices‖ * v ^ memSize t) ≤
      ‖((ghostChoiceCoeffReal F S s ρ j (2 * B) choices : ℝ) : ℂ)‖ *
        v ^ memSize (ghostOutputState F s
          (fun i => (choices i).1.1)
          (fun i => (choices i).2.1.1)
          (fun i k => (choices i).2.2 k)) := by
  classical
  let τ := ghostOutputState F s
    (fun i => (choices i).1.1)
    (fun i => (choices i).2.1.1)
    (fun i k => (choices i).2.2 k)
  let δ (t : MemPoint S.x K) : MemPoint S.x K → ℂ :=
    fun u => if u = t then 1 else 0
  let c := ghostChoiceCoeffReal F S s ρ j (2 * B) choices
  have hD (i : Fin K) :
      (choices i).1.1 ⊆ hitIndices (s.2.2 i) s.1 :=
    Finset.mem_powerset.mp (choices i).1.2
  have hterm (t : MemPoint S.x K) :
      ghostChoiceKernelTerm F S s t ρ j B choices =
        (c : ℂ) * memorySym (δ t) τ := by
    simp [ghostChoiceKernelTerm, ghostKernelTerm, ghostChoiceCoeffReal,
      ghostOutputState, δ, τ, c, hD]
  have hsize (t : MemPoint S.x K) (hδ : memorySym (δ t) τ ≠ 0) :
      memSize t = memSize τ := by
    by_contra hne
    have hzero := memorySym_delta_zero_of_memSize_ne τ t (Ne.symm hne)
    exact hδ (by simpa [δ] using hzero)
  have hsumEq :
      (∑ t ∈ T,
        ‖ghostChoiceKernelTerm F S s t ρ j B choices‖ * v ^ memSize t) =
        ∑ t ∈ T,
          ‖(c : ℂ)‖ * (‖memorySym (δ t) τ‖ * v ^ memSize t) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [hterm]
    simp [norm_mul, c]
    ring
  calc
    _ = ∑ t ∈ T,
          ‖(c : ℂ)‖ * (‖memorySym (δ t) τ‖ * v ^ memSize t) := hsumEq
    _ ≤ ∑ t ∈ T,
          ‖(c : ℂ)‖ * (‖memorySym (δ t) τ‖ * v ^ memSize τ) := by
        apply Finset.sum_le_sum
        intro t ht
        by_cases hδ : memorySym (δ t) τ = 0
        · simp [hδ]
        · rw [hsize t hδ]
    _ = ∑ t ∈ T,
          (‖(c : ℂ)‖ * v ^ memSize τ) * ‖memorySym (δ t) τ‖ := by
        apply Finset.sum_congr rfl
        intro t ht
        ring
    _ = (‖(c : ℂ)‖ * v ^ memSize τ) *
          ∑ t ∈ T, ‖memorySym (δ t) τ‖ := by
        rw [Finset.mul_sum]
    _ ≤ (‖(c : ℂ)‖ * v ^ memSize τ) * 1 := by
        apply mul_le_mul_of_nonneg_left
          (memorySym_delta_row_le τ T)
        exact mul_nonneg (norm_nonneg _) (pow_nonneg hv.le _)
    _ = ‖(c : ℂ)‖ * v ^ memSize τ := by ring

set_option maxHeartbeats 1000000 in
private theorem memGhostProjectedKernel_finite {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (j : ℕ)
    (s t : MemPoint S.x K) (B : ℕ)
    (hs : memSize s ≤ B) (ht : memSize t ≤ B) :
    memKernel (fun f => memGhost F S ρ j (memorySym f)) s t =
      ∑ D : (i : Fin K) → Finset (Fin (s.2.2 i).length),
        ∑ m ∈ GhostBatchLengths K B,
          ∑ new : (i : Fin K) → Fin (m i) → {p // p ∈ primeBand S.x (F.a i)},
            ghostKernelTerm F S s ρ j t D m new := by
  classical
  let δt : MemPoint S.x K → ℂ := fun u => if u = t then 1 else 0
  change logGhost F S ρ j (fun σL => memorySym δt σL.1) (s, []) = _
  unfold logGhost
  simp only [ghostKernelTerm, ghostOutputState]
  apply Finset.sum_congr rfl
  intro D hD
  apply tsum_eq_sum
  intro m hm
  apply Finset.sum_eq_zero
  intro new hnew
  exact ghostKernelTerm_zero_of_length_vec_notin F S s t ρ j B hs ht D m new hm

private noncomputable instance ghostGroupChoiceFintype {x : ℝ} {K : ℕ}
    (F : PDFix K) (s : MemPoint x K) (B : ℕ) (i : Fin K) :
    Fintype (GhostGroupChoice F s B i) := by
  classical
  letI : Fintype (GhostDeletionChoice s i) := ghostDeletionChoiceFintype s i
  letI : Fintype (GhostLengthChoice B) := ghostLengthChoiceFintype B
  letI : Fintype (GhostPrimeChoice (x := x) F i) := inferInstance
  infer_instance

private def ghostChoicePiEquiv {x : ℝ} {K : ℕ}
    (F : PDFix K) (s : MemPoint x K) (B : ℕ) :
    ((i : Fin K) → GhostGroupChoice F s B i) ≃
      Σ D : (i : Fin K) → GhostDeletionChoice s i,
        Σ m : (i : Fin K) → GhostLengthChoice B,
          (i : Fin K) → Fin (m i).1 → GhostPrimeChoice (x := x) F i where
  toFun choices :=
    ⟨fun i => (choices i).1,
      ⟨fun i => (choices i).2.1, fun i => (choices i).2.2⟩⟩
  invFun choices := fun i => ⟨choices.1 i, ⟨choices.2.1 i, choices.2.2 i⟩⟩
  left_inv := by
    intro choices
    funext i
    have h (c : GhostGroupChoice F s B i) :
        (⟨c.1, ⟨c.2.1, c.2.2⟩⟩ : GhostGroupChoice F s B i) = c := by
      cases c
      rfl
    exact h (choices i)
  right_inv := by
    rintro ⟨D, m, batch⟩
    apply Sigma.ext
    · funext i
      rfl
    · exact HEq.rfl

private abbrev GhostDeletionVec {x : ℝ} {K : ℕ} (s : MemPoint x K) :=
  (i : Fin K) → Finset (Fin (s.2.2 i).length)

private noncomputable def ghostGoodDeletionSet {x : ℝ} {K : ℕ} (s : MemPoint x K) :
    Finset (GhostDeletionVec s) :=
  Finset.univ.filter
    (fun D => ∀ i, D i ∈ (hitIndices (s.2.2 i) s.1).powerset)

private abbrev GhostGoodDeletionVec {x : ℝ} {K : ℕ} (s : MemPoint x K) :=
  {D : GhostDeletionVec s // D ∈ ghostGoodDeletionSet s}

private def ghostGoodDeletionVecEquiv {x : ℝ} {K : ℕ} (s : MemPoint x K) :
    GhostGoodDeletionVec s ≃ ((i : Fin K) → GhostDeletionChoice s i) where
  toFun D i := ⟨D.1 i, (Finset.mem_filter.mp D.2).2 i⟩
  invFun D := ⟨fun i => (D i).1,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i => (D i).2⟩⟩
  left_inv := by
    intro D
    apply Subtype.ext
    funext i
    rfl
  right_inv := by
    intro D
    funext i
    exact Subtype.ext rfl

private abbrev GhostBatchLengthVec (K B : ℕ) :=
  {m : Fin K → ℕ // m ∈ GhostBatchLengths K B}

private def ghostBatchLengthVecEquiv {K B : ℕ} :
    GhostBatchLengthVec K B ≃ ((i : Fin K) → GhostLengthChoice (2 * B)) where
  toFun m i := ⟨m.1 i, (Fintype.mem_piFinset.mp m.2) i⟩
  invFun m := ⟨fun i => (m i).1, by
    apply Fintype.mem_piFinset.mpr
    intro i
    exact (m i).2⟩
  left_inv := by
    intro m
    apply Subtype.ext
    rfl
  right_inv := by
    intro m
    funext i
    exact Subtype.ext rfl

private abbrev GhostBatchVec {x : ℝ} {K : ℕ} (F : PDFix K) (m : Fin K → ℕ) :=
  (i : Fin K) → Fin (m i) → GhostPrimeChoice (x := x) F i

private abbrev GhostFlatChoice {x : ℝ} {K : ℕ}
    (F : PDFix K) (s : MemPoint x K) (B : ℕ) :=
  Σ D : GhostGoodDeletionVec s,
    Σ m : GhostBatchLengthVec K B, GhostBatchVec (x := x) F m.1

private def ghostFlatToNestedEquiv {x : ℝ} {K : ℕ}
    (F : PDFix K) (s : MemPoint x K) (B : ℕ) :
    GhostFlatChoice F s B ≃
      Σ D : (i : Fin K) → GhostDeletionChoice s i,
        Σ m : (i : Fin K) → GhostLengthChoice (2 * B),
          GhostBatchVec (x := x) F (fun i => (m i).1) := by
  let eD := ghostGoodDeletionVecEquiv s
  let eM := ghostBatchLengthVecEquiv (K := K) (B := B)
  let eInner :
      (Σ m : GhostBatchLengthVec K B, GhostBatchVec (x := x) F m.1) ≃
        Σ m : ((i : Fin K) → GhostLengthChoice (2 * B)),
          GhostBatchVec (x := x) F (fun i => (m i).1) :=
    Equiv.sigmaCongr eM (fun _ => Equiv.refl _)
  exact Equiv.sigmaCongr eD (fun _ => eInner)

private def ghostFlatChoiceEquiv {x : ℝ} {K : ℕ}
    (F : PDFix K) (s : MemPoint x K) (B : ℕ) :
    GhostFlatChoice F s B ≃ ((i : Fin K) → GhostGroupChoice F s (2 * B) i) :=
  (ghostFlatToNestedEquiv F s B).trans (ghostChoicePiEquiv F s (2 * B)).symm

private def ghostFlatKernelTerm {K : ℕ}
    (F : PDFix K) (S : PDScale) (s t : MemPoint S.x K) (ρ : ℝ) (j B : ℕ)
    (c : GhostFlatChoice F s B) : ℂ :=
  ghostKernelTerm F S s ρ j t c.1.1 c.2.1.1 c.2.2

private theorem ghostFlatKernelTerm_eq_choice {K : ℕ}
    (F : PDFix K) (S : PDScale) (s t : MemPoint S.x K) (ρ : ℝ) (j B : ℕ)
    (c : GhostFlatChoice F s B) :
    ghostFlatKernelTerm F S s t ρ j B c =
      ghostChoiceKernelTerm F S s t ρ j B (ghostFlatChoiceEquiv F s B c) := by
  rfl

private theorem memGhostProjectedKernel_choiceSum {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (j : ℕ)
    (s t : MemPoint S.x K) (B : ℕ)
    (hs : memSize s ≤ B) (ht : memSize t ≤ B) :
    memKernel (fun f => memGhost F S ρ j (memorySym f)) s t =
      ∑ choices : (i : Fin K) → GhostGroupChoice F s (2 * B) i,
        ghostChoiceKernelTerm F S s t ρ j B choices := by
  classical
  rw [memGhostProjectedKernel_finite F S ρ j s t B hs ht]
  let DVec := GhostDeletionVec s
  let DGood := ghostGoodDeletionSet s
  let MVec := GhostBatchLengthVec K B
  let P : (i : Fin K) → Type := fun i => GhostPrimeChoice (x := S.x) F i
  let fD : DVec → ℂ := fun D =>
    ∑ m ∈ GhostBatchLengths K B,
      ∑ new : (i : Fin K) → Fin (m i) → P i,
        ghostKernelTerm F S s ρ j t D m new
  have hbad (D : DVec) (hD : D ∉ DGood) : fD D = 0 := by
    dsimp [fD]
    apply Finset.sum_eq_zero
    intro m hm
    apply Finset.sum_eq_zero
    intro new hnew
    have hgood : ¬ ∀ i, D i ⊆ hitIndices (s.2.2 i) s.1 := by
      intro hg
      have hset : D ∈ DGood := by
        dsimp [DGood, ghostGoodDeletionSet]
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ D, fun i => Finset.mem_powerset.mpr (hg i)⟩
      exact hD hset
    simp [ghostKernelTerm, hgood]
  have hGoodPred (D : DVec) :
      D ∈ DGood ↔
        D ∈ (Finset.univ : Finset DVec).filter
          (fun D => ∀ i, D i ∈ (hitIndices (s.2.2 i) s.1).powerset) := by
    simp [DGood, ghostGoodDeletionSet]
  have hGoodSet : DGood =
      (Finset.univ : Finset DVec).filter
        (fun D => ∀ i, D i ∈ (hitIndices (s.2.2 i) s.1).powerset) := by
    rfl
  have hDsum :
      (∑ D : DVec, fD D) = ∑ D ∈ DGood, fD D := by
    calc
      _ = ∑ D ∈ (Finset.univ : Finset DVec), fD D := by simp
      _ = ∑ D ∈ Finset.univ, if D ∈ DGood then fD D else 0 := by
        apply Finset.sum_congr rfl
        intro D hD
        by_cases hg : D ∈ DGood
        · simp [hg]
        · simp [hg, hbad D hg]
      _ = ∑ D ∈ Finset.univ,
            if ∀ i, D i ∈ (hitIndices (s.2.2 i) s.1).powerset then fD D else 0 := by
        apply Finset.sum_congr rfl
        intro D hD
        simp [DGood, ghostGoodDeletionSet]
      _ = ∑ D ∈ DGood, fD D := by
        symm
        rw [hGoodSet, Finset.sum_filter]
  have hDsub :
      (∑ D ∈ DGood, fD D) = ∑ d : GhostGoodDeletionVec s, fD d.1 := by
    symm
    exact sum_subtype_eq_sum_finset DGood fD
  rw [hDsum, hDsub]
  have hM (d : GhostGoodDeletionVec s) :
      (∑ m ∈ GhostBatchLengths K B,
        ∑ new : (i : Fin K) → Fin (m i) → P i,
          ghostKernelTerm F S s ρ j t d.1 m new) =
        ∑ m : GhostBatchLengthVec K B,
          ∑ new : GhostBatchVec (x := S.x) F m.1,
            ghostKernelTerm F S s ρ j t d.1 m.1 new := by
    symm
    exact sum_subtype_eq_sum_finset (GhostBatchLengths K B)
      (fun m => ∑ new : (i : Fin K) → Fin (m i) → P i,
        ghostKernelTerm F S s ρ j t d.1 m new)
  calc
    _ = ∑ d : GhostGoodDeletionVec s,
          ∑ m : GhostBatchLengthVec K B,
            ∑ new : GhostBatchVec (x := S.x) F m.1,
              ghostKernelTerm F S s ρ j t d.1 m.1 new := by
        apply Finset.sum_congr rfl
        intro d hd
        exact hM d
    _ = ∑ c : GhostFlatChoice F s B, ghostFlatKernelTerm F S s t ρ j B c := by
        symm
        simp only [Fintype.sum_sigma, ghostFlatKernelTerm]
    _ = ∑ choices : (i : Fin K) → GhostGroupChoice F s (2 * B) i,
          ghostFlatKernelTerm F S s t ρ j B
            ((ghostFlatChoiceEquiv F s B).symm choices) := by
        exact Equiv.sum_comp (ghostFlatChoiceEquiv F s B)
          (fun choices => ghostFlatKernelTerm F S s t ρ j B
            ((ghostFlatChoiceEquiv F s B).symm choices))
    _ = _ := by
        apply Finset.sum_congr rfl
        intro choices hchoices
        calc
          ghostFlatKernelTerm F S s t ρ j B ((ghostFlatChoiceEquiv F s B).symm choices) =
              ghostChoiceKernelTerm F S s t ρ j B
                (ghostFlatChoiceEquiv F s B
                  ((ghostFlatChoiceEquiv F s B).symm choices)) :=
            ghostFlatKernelTerm_eq_choice F S s t ρ j B _
          _ = ghostChoiceKernelTerm F S s t ρ j B choices := by
            rw [(ghostFlatChoiceEquiv F s B).apply_symm_apply]

private theorem ghostChoicePi_sum_flatten {x : ℝ} {K : ℕ}
    (F : PDFix K) (s : MemPoint x K) (B : ℕ)
    (g : ((i : Fin K) → GhostGroupChoice F s B i) → ℝ) :
    (∑ choices : (i : Fin K) → GhostGroupChoice F s B i, g choices) =
      ∑ D : (i : Fin K) → GhostDeletionChoice s i,
        ∑ m : (i : Fin K) → GhostLengthChoice B,
          ∑ batch : (i : Fin K) → Fin (m i).1 → GhostPrimeChoice (x := x) F i,
            g ((ghostChoicePiEquiv F s B).symm ⟨D, ⟨m, batch⟩⟩) := by
  classical
  rw [← Equiv.sum_comp (ghostChoicePiEquiv F s B).symm g]
  simp only [Fintype.sum_sigma]

private def ghostGroupFiniteWeight {x : ℝ} {K : ℕ}
    (F : PDFix K) (s : MemPoint x K) (B : ℕ) (j : ℕ) (ρ v : ℝ)
    (i : Fin K) (c : GhostGroupChoice F s B i) : ℝ :=
  (memoryEta x F.q_d j / (ρ * v)) ^ c.1.1.card *
    (memoryQ x F.q_d j / ρ ^ 2) ^
      ((hitIndices (s.2.2 i) s.1).card - c.1.1.card) *
    ((memoryEta x F.q_d j * bandMass x (F.a i) / ρ * v) ^ c.2.1.1 /
      (c.2.1.1.factorial : ℝ) *
      ∏ k : Fin c.2.1.1, memoryNu x K F.a F.q_d i (c.2.2 k).1)

private def ghostGroupColumnFiniteWeight {K : ℕ}
    (F : PDFix K) (S : PDScale) (s : MemPoint S.x K) (B j : ℕ)
    (ρ v : ℝ) (i : Fin K) (c : GhostGroupChoice F s B i) : ℝ :=
  ghostGroupFiniteWeight F s B j ρ (v / bandMass S.x (F.a i)) i c

private theorem ghost_interleave_factorial_measure (n d : ℕ) :
    (Nat.choose (n + d) d : ℝ) / ((n + d).factorial : ℝ) =
      1 / ((n.factorial : ℝ) * (d.factorial : ℝ)) := by
  have hsub : n + d - d = n := by omega
  have hNat := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left d n)
  rw [hsub] at hNat
  have hReal : (Nat.choose (n + d) d : ℝ) * (d.factorial : ℝ) *
      (n.factorial : ℝ) = ((n + d).factorial : ℝ) := by
    exact_mod_cast hNat
  have hn : 0 < (n.factorial : ℝ) := by positivity
  have hd : 0 < (d.factorial : ℝ) := by positivity
  have htotal : 0 < ((n + d).factorial : ℝ) := by positivity
  field_simp [ne_of_gt hn, ne_of_gt hd, ne_of_gt htotal]
  nlinarith [hReal]

private theorem ghost_interleave_factorial_active (n d : ℕ) :
    (Nat.choose (n + d) d : ℝ) * (d.factorial : ℝ) /
      ((n + d).factorial : ℝ) = 1 / (n.factorial : ℝ) := by
  have hsub : n + d - d = n := by omega
  have hNat := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left d n)
  rw [hsub] at hNat
  have hReal : (Nat.choose (n + d) d : ℝ) * (d.factorial : ℝ) *
      (n.factorial : ℝ) = ((n + d).factorial : ℝ) := by
    exact_mod_cast hNat
  have hn : 0 < (n.factorial : ℝ) := by positivity
  have hd : 0 < (d.factorial : ℝ) := by positivity
  have htotal : 0 < ((n + d).factorial : ℝ) := by positivity
  field_simp [ne_of_gt hn, ne_of_gt hd, ne_of_gt htotal]
  nlinarith [hReal]

private theorem ghostGroupFiniteWeight_mul_pow_eq_normCoeff_mul_pow {K : ℕ}
    (F : PDFix K) (S : PDScale) (s : MemPoint S.x K) (B j : ℕ)
    (ρ v : ℝ) (i : Fin K)
    (c : GhostGroupChoice F s B i) (hη : 0 ≤ memoryEta S.x F.q_d j)
    (hq : 0 ≤ memoryQ S.x F.q_d j) (hV : 0 ≤ bandMass S.x (F.a i))
    (hρ : 0 < ρ) (hv : 0 < v)
    (hν : ∀ k : Fin c.2.1.1,
      0 ≤ memoryNu S.x K F.a F.q_d i (c.2.2 k).1) :
    ghostGroupFiniteWeight F s B j ρ v i c * v ^ c.1.1.card =
      ‖((ghostGroupCoeff F S ρ j i
        (hitCount (s.2.2 i) s.1) c.1.1.card c.2.1.1
        (List.ofFn fun k => (c.2.2 k).1) : ℝ) : ℂ)‖ * v ^ c.2.1.1 := by
  classical
  let η := memoryEta S.x F.q_d j
  let q := memoryQ S.x F.q_d j
  let V := bandMass S.x (F.a i)
  let d := c.1.1.card
  let l := c.2.1.1
  let b := (hitIndices (s.2.2 i) s.1).card - d
  let ν := ∏ k : Fin l, memoryNu S.x K F.a F.q_d i (c.2.2 k).1
  have hηρ : 0 ≤ η / ρ := div_nonneg hη hρ.le
  have hqρ : 0 ≤ q / ρ ^ 2 := div_nonneg hq (sq_nonneg ρ)
  have hηVρ : 0 ≤ η * V / ρ := div_nonneg (mul_nonneg hη hV) hρ.le
  have hν' : 0 ≤ ν := Finset.prod_nonneg fun k hk => hν k
  have hfac : 0 < (l.factorial : ℝ) := by positivity
  have hnorm :
      ‖((ghostGroupCoeff F S ρ j i (hitCount (s.2.2 i) s.1) d l
        (List.ofFn fun k => (c.2.2 k).1) : ℝ) : ℂ)‖ =
        (η / ρ) ^ d * (q / ρ ^ 2) ^ b *
          ((η * V / ρ) ^ l / (l.factorial : ℝ) * ν) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    unfold ghostGroupCoeff
    rw [List.map_ofFn, List.prod_ofFn]
    simp [hitCount, η, q, V, d, l, b, ν, abs_mul, abs_pow,
      abs_div, abs_neg, abs_of_pos hρ, abs_of_nonneg hη, abs_of_nonneg hq,
      abs_of_nonneg hV, abs_of_nonneg hν', abs_of_nonneg hfac.le,
      List.prod_ofFn] <;> ring_nf
  have hdel : (η / (ρ * v)) ^ d * v ^ d = (η / ρ) ^ d := by
    rw [← mul_pow]
    congr 1
    field_simp [ne_of_gt hρ, ne_of_gt hv]
  have hbirth : (η * V / ρ * v) ^ l = (η * V / ρ) ^ l * v ^ l := by
    rw [mul_pow]
  calc
    _ = ((η / (ρ * v)) ^ d * (q / ρ ^ 2) ^ b *
          ((η * V / ρ * v) ^ l / (l.factorial : ℝ) * ν)) * v ^ d := by
        simp [ghostGroupFiniteWeight, η, q, V, d, l, b, ν]
    _ = ((η / ρ) ^ d * (q / ρ ^ 2) ^ b *
          ((η * V / ρ) ^ l / (l.factorial : ℝ) * ν)) * v ^ l := by
        rw [hbirth]
        calc
          _ = ((η / (ρ * v)) ^ d * v ^ d) * (q / ρ ^ 2) ^ b *
                (((η * V / ρ) ^ l * v ^ l) / (l.factorial : ℝ) * ν) := by ring
          _ = _ := by rw [hdel]; ring
    _ = ‖((ghostGroupCoeff F S ρ j i (hitCount (s.2.2 i) s.1) d l
          (List.ofFn fun k => (c.2.2 k).1) : ℝ) : ℂ)‖ * v ^ l := by
        rw [hnorm]

private theorem ghost_group_batch_summable {K : ℕ} (F : PDFix K)
    (i : Fin K) {x : ℝ} (c : ℝ) :
    Summable (fun l : ℕ =>
      ∑ batch : Fin l → {p // p ∈ primeBand x (F.a i)},
        c ^ l / (l.factorial : ℝ) *
          ∏ k : Fin l, memoryNu x K F.a F.q_d i (batch k).1) := by
  classical
  let P := primeBand x (F.a i)
  let α := {p // p ∈ P}
  letI : Fintype α := Fintype.ofFinset P (by intro p; simp [P])
  let ν : α → ℝ := fun p => memoryNu x K F.a F.q_d i p.1
  let s : ℝ := ∑ p : α, ν p
  have hinner (l : ℕ) :
      (∑ batch : Fin l → α,
        c ^ l / (l.factorial : ℝ) * ∏ k : Fin l, ν (batch k)) =
        (c * s) ^ l / (l.factorial : ℝ) := by
    calc
      _ = c ^ l / (l.factorial : ℝ) *
            ∑ batch : Fin l → α, ∏ k : Fin l, ν (batch k) := by
              rw [← Finset.mul_sum]
      _ = c ^ l / (l.factorial : ℝ) * s ^ l := by
              rw [sum_fin_function_prod]
      _ = (c * s) ^ l / (l.factorial : ℝ) := by
              calc
                c ^ l / (l.factorial : ℝ) * s ^ l =
                    (c ^ l * s ^ l) / (l.factorial : ℝ) := by ring
                _ = (c * s) ^ l / (l.factorial : ℝ) := by rw [← mul_pow]
  have hs : Summable (fun l : ℕ => (c * s) ^ l / (l.factorial : ℝ)) :=
    (NormedSpace.expSeries_div_hasSum_exp (c * s)).summable
  have heq :
      (fun l : ℕ =>
        ∑ batch : Fin l → {p // p ∈ primeBand x (F.a i)},
          c ^ l / (l.factorial : ℝ) *
            ∏ k : Fin l, memoryNu x K F.a F.q_d i (batch k).1) =
        fun l : ℕ => (c * s) ^ l / (l.factorial : ℝ) := by
    funext l
    simpa [P, α, ν, s] using hinner l
  exact heq ▸ hs

private theorem ghost_group_finite_choice_le_exp {K : ℕ} (F : PDFix K)
    (hF : F.Valid) (i : Fin K) (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ)
    (v : ℝ) (hv : 0 < v)
    (hvlarge : 2 / (ρ * (1 - Real.sqrt F.q_d / ρ ^ 2)) ≤ v)
    {x : ℝ} (hV : 0 < bandMass x (F.a i))
    (hbp : ∀ p ∈ markedPrimes x K F.a,
      (1 / 2 : ℝ) ≤ memoryBPrime x F.q_d p)
    (j : ℕ) (l : List Particle) (z : ℤ × ℤ) (B : ℕ) :
    (∑ D ∈ (hitIndices l z).powerset,
      ∑ m ∈ Finset.range (B + 1),
        ∑ batch : Fin m → {p // p ∈ primeBand x (F.a i)},
          (memoryEta x F.q_d j / (ρ * v)) ^ D.card *
            (memoryQ x F.q_d j / ρ ^ 2) ^ ((hitIndices l z).card - D.card) *
            ((memoryEta x F.q_d j * bandMass x (F.a i) / ρ * v) ^ m /
              (m.factorial : ℝ) *
              ∏ k : Fin m, memoryNu x K F.a F.q_d i (batch k).1)) ≤
      Real.exp (2 * memoryEta x F.q_d j * bandMass x (F.a i) * v / ρ) := by
  classical
  let c := memoryEta x F.q_d j * bandMass x (F.a i) / ρ * v
  let a := memoryEta x F.q_d j / (ρ * v)
  let b := memoryQ x F.q_d j / ρ ^ 2
  let birth : ℕ → ℝ := fun m =>
    ∑ batch : Fin m → {p // p ∈ primeBand x (F.a i)},
      c ^ m / (m.factorial : ℝ) *
        ∏ k : Fin m, memoryNu x K F.a F.q_d i (batch k).1
  let coeff : Finset (Fin l.length) → ℝ := fun D =>
    a ^ D.card * b ^ ((hitIndices l z).card - D.card)
  have hρpos := hρ.1
  have hvρ : 0 < ρ * v := mul_pos hρpos hv
  have hqjlt : memoryQ x F.q_d j < 1 := by
    have hρsq : ρ ^ 2 < 1 := by nlinarith [hρ.1, hρ.2.1]
    have hrootltone : Real.sqrt F.q_d < 1 := lt_trans hρ.2.2 hρsq
    unfold memoryQ
    split_ifs <;> [exact hrootltone; exact hF.2.2.1]
  have hη : 0 ≤ memoryEta x F.q_d j := by
    unfold memoryEta
    linarith
  have hqnonneg : 0 ≤ memoryQ x F.q_d j := by
    unfold memoryQ
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact hF.2.1.le
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have ha : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg hη hvρ.le
  have hb : 0 ≤ b := by
    dsimp [b]
    exact div_nonneg hqnonneg (sq_nonneg ρ)
  have hbirthSum : Summable birth := by
    dsimp [birth]
    exact ghost_group_batch_summable F i c
  have hbirthNonneg (m : ℕ) : 0 ≤ birth m := by
    dsimp [birth]
    apply Finset.sum_nonneg
    intro batch hbatch
    apply mul_nonneg
    · exact div_nonneg (pow_nonneg hc _) (Nat.cast_nonneg _)
    · apply Finset.prod_nonneg
      intro k hk
      have hbp' : 0 < memoryBPrime x F.q_d (batch k).1 :=
        lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
          (hbp (batch k).1 (Finset.mem_biUnion.mpr
            ⟨i, Finset.mem_univ i, (batch k).2⟩))
      have hden : 0 < bandMass x (F.a i) * (((batch k).1 : ℝ) + 1) *
          memoryBPrime x F.q_d (batch k).1 := by positivity
      unfold memoryNu
      exact div_nonneg (by norm_num) hden.le
  have hcoeffNonneg (D : Finset (Fin l.length)) : 0 ≤ coeff D := by
    dsimp [coeff]
    exact mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _)
  have hpartial (D : Finset (Fin l.length)) :
      (∑ m ∈ Finset.range (B + 1),
        ∑ batch : Fin m → {p // p ∈ primeBand x (F.a i)},
          coeff D * (c ^ m / (m.factorial : ℝ) *
            ∏ k : Fin m, memoryNu x K F.a F.q_d i (batch k).1)) ≤
        coeff D * ∑' m : ℕ, birth m := by
    have hsum : Summable (fun m : ℕ => coeff D * birth m) :=
      hbirthSum.mul_left (coeff D)
    have hnonneg (m : ℕ) : 0 ≤ coeff D * birth m :=
      mul_nonneg (hcoeffNonneg D) (hbirthNonneg m)
    have hrewrite :
        (∑ m ∈ Finset.range (B + 1),
          ∑ batch : Fin m → {p // p ∈ primeBand x (F.a i)},
            coeff D * (c ^ m / (m.factorial : ℝ) *
              ∏ k : Fin m, memoryNu x K F.a F.q_d i (batch k).1)) =
          ∑ m ∈ Finset.range (B + 1), coeff D * birth m := by
      apply Finset.sum_congr rfl
      intro m hm
      simp [birth, Finset.mul_sum, mul_assoc]
    rw [hrewrite]
    calc
      _ ≤ ∑' m : ℕ, coeff D * birth m :=
        Summable.sum_le_tsum (Finset.range (B + 1))
          (by intro m hm; exact hnonneg m) hsum
      _ = coeff D * ∑' m : ℕ, birth m := by rw [tsum_mul_left]
  calc
    _ ≤ ∑ D ∈ (hitIndices l z).powerset,
          coeff D * ∑' m : ℕ, birth m := by
        apply Finset.sum_le_sum
        intro D hD
        exact hpartial D
    _ ≤ Real.exp (2 * memoryEta x F.q_d j * bandMass x (F.a i) * v / ρ) := by
        simpa [c, a, b, birth, coeff, mul_assoc] using
          ghost_group_choice_sum_le_exp F hF i ρ hρ v hv hvlarge hV hbp j l z

set_option maxHeartbeats 1000000 in
private theorem ghost_group_choice_sum_eq {x : ℝ} {K : ℕ}
    (F : PDFix K) (s : MemPoint x K) (B j : ℕ) (ρ v : ℝ) (i : Fin K) :
    (∑ c : GhostGroupChoice F s B i, ghostGroupFiniteWeight F s B j ρ v i c) =
      ∑ D ∈ (hitIndices (s.2.2 i) s.1).powerset,
        ∑ m ∈ Finset.range (B + 1),
          ∑ batch : Fin m → {p // p ∈ primeBand x (F.a i)},
            (memoryEta x F.q_d j / (ρ * v)) ^ D.card *
              (memoryQ x F.q_d j / ρ ^ 2) ^
                ((hitIndices (s.2.2 i) s.1).card - D.card) *
              ((memoryEta x F.q_d j * bandMass x (F.a i) / ρ * v) ^ m /
                (m.factorial : ℝ) *
                ∏ k : Fin m, memoryNu x K F.a F.q_d i (batch k).1) := by
  classical
  let H := hitIndices (s.2.2 i) s.1
  let Dset := H.powerset
  let Mset := Finset.range (B + 1)
  let DType := {D // D ∈ Dset}
  let MType := {m // m ∈ Mset}
  let PType := {p // p ∈ primeBand x (F.a i)}
  let f : Finset (Fin (s.2.2 i).length) → ℝ := fun D =>
    ∑ m : MType, ∑ batch : Fin m.1 → PType,
      if hD : D ∈ Dset then
        ghostGroupFiniteWeight F s B j ρ v i ⟨⟨D, hD⟩, ⟨m, batch⟩⟩
      else 0
  change (∑ c : Σ D : DType, Σ m : MType, Fin m.1 → PType,
      ghostGroupFiniteWeight F s B j ρ v i c) = _
  simp only [Fintype.sum_sigma]
  calc
    _ = ∑ D : DType, f D.1 := by
        apply Finset.sum_congr rfl
        intro D hD
        simp [f]
    _ = ∑ D ∈ Dset, f D := sum_subtype_eq_sum_finset Dset f
    _ = ∑ D ∈ Dset, ∑ m : MType, ∑ batch : Fin m.1 → PType,
          (memoryEta x F.q_d j / (ρ * v)) ^ D.card *
            (memoryQ x F.q_d j / ρ ^ 2) ^ (H.card - D.card) *
            ((memoryEta x F.q_d j * bandMass x (F.a i) / ρ * v) ^ m.1 /
              (m.1.factorial : ℝ) *
              ∏ k : Fin m.1, memoryNu x K F.a F.q_d i (batch k).1) := by
        apply Finset.sum_congr rfl
        intro D hD
        simp [f, hD, ghostGroupFiniteWeight, H]
    _ = ∑ D ∈ Dset, ∑ m ∈ Mset, ∑ batch : Fin m → PType,
          (memoryEta x F.q_d j / (ρ * v)) ^ D.card *
            (memoryQ x F.q_d j / ρ ^ 2) ^ (H.card - D.card) *
            ((memoryEta x F.q_d j * bandMass x (F.a i) / ρ * v) ^ m /
              (m.factorial : ℝ) *
              ∏ k : Fin m, memoryNu x K F.a F.q_d i (batch k).1) := by
        apply Finset.sum_congr rfl
        intro D hD
        exact sum_subtype_eq_sum_finset Mset (fun m =>
          ∑ batch : Fin m → PType,
            (memoryEta x F.q_d j / (ρ * v)) ^ D.card *
              (memoryQ x F.q_d j / ρ ^ 2) ^ (H.card - D.card) *
              ((memoryEta x F.q_d j * bandMass x (F.a i) / ρ * v) ^ m /
                (m.factorial : ℝ) *
                ∏ k : Fin m, memoryNu x K F.a F.q_d i (batch k).1))
    _ = _ := by rfl

private def ghostChoicesOutput {x : ℝ} {K : ℕ}
    (F : PDFix K) (s : MemPoint x K) (B : ℕ)
    (choices : (i : Fin K) → GhostGroupChoice F s B i) : MemPoint x K :=
  (s.1, s.2.1, fun i =>
    removeIndices (s.2.2 i) (choices i).1.1 ++
      List.ofFn fun k => anchorAt ((choices i).2.2 k).1 s.1)

private theorem ghostChoicesOutput_memSize {x : ℝ} {K : ℕ}
    (F : PDFix K) (s : MemPoint x K) (B : ℕ)
    (choices : (i : Fin K) → GhostGroupChoice F s B i) :
    memSize (ghostChoicesOutput F s B choices) =
      ∑ i : Fin K,
        ((s.2.2 i).length - (choices i).1.1.card + (choices i).2.1.1) := by
  simp [memSize, ghostChoicesOutput, removeIndices_length]

private theorem ghostChoicesOutput_memSize_gt_of_large_batch {x : ℝ} {K : ℕ}
    (F : PDFix K) (s : MemPoint x K) (B : ℕ)
    (choices : (i : Fin K) → GhostGroupChoice F s (2 * B) i)
    (hsize : memSize s ≤ B) (i : Fin K)
    (hm : 2 * B < (choices i).2.1.1) :
    B < memSize (ghostChoicesOutput F s (2 * B) choices) := by
  rw [ghostChoicesOutput_memSize]
  have hlen : (s.2.2 i).length ≤ B := by
    have hle : (s.2.2 i).length ≤ memSize s := by
      unfold memSize
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun k : Fin K => (s.2.2 k).length)
        (by intro k hk; exact Nat.zero_le _) (Finset.mem_univ i)
    exact hle.trans hsize
  have hdel : (choices i).1.1.card ≤ (s.2.2 i).length := by
    simpa using Finset.card_le_univ (choices i).1.1
  have hgroup : B < (s.2.2 i).length - (choices i).1.1.card + (choices i).2.1.1 := by
    omega
  have hsum :
      (s.2.2 i).length - (choices i).1.1.card + (choices i).2.1.1 ≤
        ∑ k : Fin K,
          ((s.2.2 k).length - (choices k).1.1.card + (choices k).2.1.1) :=
    Finset.single_le_sum (s := Finset.univ)
      (f := fun k : Fin K =>
        (s.2.2 k).length - (choices k).1.1.card + (choices k).2.1.1)
      (by intro k hk; omega) (Finset.mem_univ i)
  exact hgroup.trans_le hsum

set_option maxHeartbeats 1000000 in
private theorem ghost_all_group_choices_le_exp {x : ℝ} {K : ℕ}
    (F : PDFix K) (hF : F.Valid) (s : MemPoint x K) (B j : ℕ)
    (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ) (v : ℝ) (hv : 0 < v)
    (hvlarge : 2 / (ρ * (1 - Real.sqrt F.q_d / ρ ^ 2)) ≤ v)
    (hV : ∀ i : Fin K, 0 < bandMass x (F.a i))
    (hbp : ∀ p ∈ markedPrimes x K F.a,
      (1 / 2 : ℝ) ≤ memoryBPrime x F.q_d p) :
    (∑ choices : (i : Fin K) → GhostGroupChoice F s B i,
      ∏ i : Fin K, ghostGroupFiniteWeight F s B j ρ v i (choices i)) ≤
      ∏ i : Fin K,
        Real.exp (2 * memoryEta x F.q_d j * bandMass x (F.a i) * v / ρ) := by
  have hρpos := hρ.1
  have hρsq : ρ ^ 2 < 1 := by nlinarith [hρ.1, hρ.2.1]
  have hrootltone : Real.sqrt F.q_d < 1 := lt_trans hρ.2.2 hρsq
  have hqjlt : memoryQ x F.q_d j < 1 := by
    unfold memoryQ
    split_ifs <;> [exact hrootltone; exact hF.2.2.1]
  have hη : 0 ≤ memoryEta x F.q_d j := by
    unfold memoryEta
    linarith
  have hqnonneg : 0 ≤ memoryQ x F.q_d j := by
    unfold memoryQ
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact hF.2.1.le
  have hρv : 0 < ρ * v := mul_pos hρpos hv
  have ha : 0 ≤ memoryEta x F.q_d j / (ρ * v) := div_nonneg hη hρv.le
  have hb : 0 ≤ memoryQ x F.q_d j / ρ ^ 2 :=
    div_nonneg hqnonneg (sq_nonneg ρ)
  have hc (i : Fin K) :
      0 ≤ memoryEta x F.q_d j * bandMass x (F.a i) / ρ * v := by
    exact mul_nonneg
      (div_nonneg (mul_nonneg hη (hV i).le) hρpos.le) hv.le
  have hν (i : Fin K) (p : GhostPrimeChoice (x := x) F i) :
      0 ≤ memoryNu x K F.a F.q_d i p.1 := by
    have hbp' : 0 < memoryBPrime x F.q_d p.1 :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
        (hbp p.1 (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, p.2⟩))
    have hden : 0 < bandMass x (F.a i) * ((p.1 : ℝ) + 1) *
        memoryBPrime x F.q_d p.1 :=
      mul_pos (mul_pos (hV i) (by positivity)) hbp'
    unfold memoryNu
    exact div_nonneg (by norm_num) hden.le
  have hlocalNonneg (i : Fin K) :
      0 ≤ ∑ c : GhostGroupChoice F s B i,
        ghostGroupFiniteWeight F s B j ρ v i c := by
    rw [ghost_group_choice_sum_eq]
    apply Finset.sum_nonneg
    intro D hD
    apply Finset.sum_nonneg
    intro m hm
    apply Finset.sum_nonneg
    intro batch hbatch
    have hdel :
        0 ≤ (memoryEta x F.q_d j / (ρ * v)) ^ D.card *
          (memoryQ x F.q_d j / ρ ^ 2) ^
            ((hitIndices (s.2.2 i) s.1).card - D.card) :=
      mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _)
    have hbth : 0 ≤
        (memoryEta x F.q_d j * bandMass x (F.a i) / ρ * v) ^ m /
          (m.factorial : ℝ) *
          ∏ k : Fin m, memoryNu x K F.a F.q_d i (batch k).1 := by
      apply mul_nonneg
      · exact div_nonneg (pow_nonneg (hc i) _) (Nat.cast_nonneg _)
      · exact Finset.prod_nonneg fun k hk => hν i (batch k)
    exact mul_nonneg hdel hbth
  have hlocalBound (i : Fin K) :
      (∑ c : GhostGroupChoice F s B i,
        ghostGroupFiniteWeight F s B j ρ v i c) ≤
        Real.exp (2 * memoryEta x F.q_d j * bandMass x (F.a i) * v / ρ) := by
    rw [ghost_group_choice_sum_eq]
    exact ghost_group_finite_choice_le_exp F hF i ρ hρ v hv hvlarge
      (hV i) hbp j (s.2.2 i) s.1 B
  calc
    _ = ∏ i : Fin K,
        ∑ c : GhostGroupChoice F s B i,
          ghostGroupFiniteWeight F s B j ρ v i c :=
      finite_pi_sum_prod (fun i => GhostGroupChoice F s B i)
        (fun i c => ghostGroupFiniteWeight F s B j ρ v i c)
    _ ≤ _ := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact hlocalNonneg i
      · intro i hi
        exact hlocalBound i

private theorem ghost_group_column_choice_sum_le_exp {K : ℕ}
    (F : PDFix K) (hF : F.Valid) (S : PDScale) (s : MemPoint S.x K)
    (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ) (i : Fin K) (j B : ℕ) (v : ℝ)
    (hv : 0 < v)
    (hvlarge : 2 * bandMass S.x (F.a i) /
      (ρ * (1 - Real.sqrt F.q_d / ρ ^ 2)) ≤ v)
    (hV : 0 < bandMass S.x (F.a i))
    (hbp : ∀ p ∈ markedPrimes S.x K F.a,
      (1 / 2 : ℝ) ≤ memoryBPrime S.x F.q_d p) :
    (∑ c : GhostGroupChoice F s B i,
      ghostGroupColumnFiniteWeight F S s B j ρ v i c) ≤
      Real.exp (2 * memoryEta S.x F.q_d j * v / ρ) := by
  classical
  let V := bandMass S.x (F.a i)
  let v' := v / V
  have hv' : 0 < v' := div_pos hv hV
  have hg : 0 < 1 - Real.sqrt F.q_d / ρ ^ 2 := by
    have hsq : 0 < ρ ^ 2 := sq_pos_of_pos hρ.1
    apply sub_pos.mpr
    exact (div_lt_one₀ hsq).2 hρ.2.2
  have hv'large : 2 / (ρ * (1 - Real.sqrt F.q_d / ρ ^ 2)) ≤ v' := by
    change 2 / (ρ * (1 - Real.sqrt F.q_d / ρ ^ 2)) ≤
      v / bandMass S.x (F.a i)
    rw [le_div_iff₀ hV]
    have hmul :
        (2 / (ρ * (1 - Real.sqrt F.q_d / ρ ^ 2))) * V =
          2 * V / (ρ * (1 - Real.sqrt F.q_d / ρ ^ 2)) := by ring
    rw [hmul]
    exact hvlarge
  have hbase :
      (∑ c : GhostGroupChoice F s B i,
        ghostGroupFiniteWeight F s B j ρ v' i c) ≤
        Real.exp (2 * memoryEta S.x F.q_d j * V * v' / ρ) := by
    rw [ghost_group_choice_sum_eq]
    exact ghost_group_finite_choice_le_exp F hF i ρ hρ v' hv' hv'large
      hV hbp j (s.2.2 i) s.1 B
  change (∑ c : GhostGroupChoice F s B i,
      ghostGroupFiniteWeight F s B j ρ v' i c) ≤ _
  calc
    _ ≤ Real.exp (2 * memoryEta S.x F.q_d j * V * v' / ρ) := hbase
    _ = Real.exp (2 * memoryEta S.x F.q_d j * v / ρ) := by
      congr 1
      dsimp [v', V]
      field_simp [ne_of_gt hV, ne_of_gt hρ.1]
      <;> ring

private theorem ghost_all_group_column_choices_le_exp {K : ℕ}
    (F : PDFix K) (hF : F.Valid) (S : PDScale) (s : MemPoint S.x K)
    (B j : ℕ) (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ) (v : ℝ) (hv : 0 < v)
    (hvlarge : ∀ i : Fin K,
      2 * bandMass S.x (F.a i) /
        (ρ * (1 - Real.sqrt F.q_d / ρ ^ 2)) ≤ v)
    (hV : ∀ i : Fin K, 0 < bandMass S.x (F.a i))
    (hbp : ∀ p ∈ markedPrimes S.x K F.a,
      (1 / 2 : ℝ) ≤ memoryBPrime S.x F.q_d p) :
    (∑ choices : (i : Fin K) → GhostGroupChoice F s B i,
      ∏ i : Fin K, ghostGroupColumnFiniteWeight F S s B j ρ v i (choices i)) ≤
      ∏ i : Fin K, Real.exp (2 * memoryEta S.x F.q_d j * v / ρ) := by
  classical
  have hρpos := hρ.1
  have hρsq : ρ ^ 2 < 1 := by nlinarith [hρ.1, hρ.2.1]
  have hrootltone : Real.sqrt F.q_d < 1 := lt_trans hρ.2.2 hρsq
  have hqjlt : memoryQ S.x F.q_d j < 1 := by
    unfold memoryQ
    split_ifs <;> [exact hrootltone; exact hF.2.2.1]
  have hη : 0 ≤ memoryEta S.x F.q_d j := by
    unfold memoryEta
    linarith [hqjlt]
  have hq : 0 ≤ memoryQ S.x F.q_d j := by
    unfold memoryQ
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact hF.2.1.le
  have hν (i : Fin K) (p : GhostPrimeChoice (x := S.x) F i) :
      0 ≤ memoryNu S.x K F.a F.q_d i p.1 := by
    have hbp' : 0 < memoryBPrime S.x F.q_d p.1 :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
        (hbp p.1 (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, p.2⟩))
    have hden : 0 < bandMass S.x (F.a i) * ((p.1 : ℝ) + 1) *
        memoryBPrime S.x F.q_d p.1 :=
      mul_pos (mul_pos (hV i) (by positivity)) hbp'
    unfold memoryNu
    exact div_nonneg (by norm_num) hden.le
  have hlocalNonneg (i : Fin K) :
      0 ≤ ∑ c : GhostGroupChoice F s B i,
        ghostGroupColumnFiniteWeight F S s B j ρ v i c := by
    change 0 ≤ ∑ c : GhostGroupChoice F s B i,
      ghostGroupFiniteWeight F s B j ρ (v / bandMass S.x (F.a i)) i c
    rw [ghost_group_choice_sum_eq]
    let vi := v / bandMass S.x (F.a i)
    have hρvi : 0 < ρ * vi := mul_pos hρpos (div_pos hv (hV i))
    have ha : 0 ≤ memoryEta S.x F.q_d j / (ρ * vi) :=
      div_nonneg hη hρvi.le
    have hb : 0 ≤ memoryQ S.x F.q_d j / ρ ^ 2 :=
      div_nonneg hq (sq_nonneg ρ)
    have hc : 0 ≤ memoryEta S.x F.q_d j * bandMass S.x (F.a i) / ρ * vi := by
      exact mul_nonneg
        (div_nonneg (mul_nonneg hη (hV i).le) hρpos.le) (div_pos hv (hV i)).le
    apply Finset.sum_nonneg
    intro D hD
    apply Finset.sum_nonneg
    intro m hm
    apply Finset.sum_nonneg
    intro batch hbatch
    have hdel :
        0 ≤ (memoryEta S.x F.q_d j / (ρ * vi)) ^ D.card *
          (memoryQ S.x F.q_d j / ρ ^ 2) ^
            ((hitIndices (s.2.2 i) s.1).card - D.card) :=
      mul_nonneg (pow_nonneg ha _) (pow_nonneg hb _)
    have hbth : 0 ≤
        (memoryEta S.x F.q_d j * bandMass S.x (F.a i) / ρ * vi) ^ m /
          (m.factorial : ℝ) *
          ∏ k : Fin m, memoryNu S.x K F.a F.q_d i (batch k).1 := by
      apply mul_nonneg
      · exact div_nonneg (pow_nonneg hc _) (Nat.cast_nonneg _)
      · exact Finset.prod_nonneg fun k hk => hν i (batch k)
    exact mul_nonneg hdel hbth
  have hlocalBound (i : Fin K) :
      (∑ c : GhostGroupChoice F s B i,
        ghostGroupColumnFiniteWeight F S s B j ρ v i c) ≤
        Real.exp (2 * memoryEta S.x F.q_d j * v / ρ) :=
    ghost_group_column_choice_sum_le_exp F hF S s ρ hρ i j B v hv
      (hvlarge i) (hV i) hbp
  calc
    _ = ∏ i : Fin K,
        ∑ c : GhostGroupChoice F s B i,
          ghostGroupColumnFiniteWeight F S s B j ρ v i c :=
      finite_pi_sum_prod (fun i => GhostGroupChoice F s B i)
        (fun i c => ghostGroupColumnFiniteWeight F S s B j ρ v i c)
    _ ≤ _ := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact hlocalNonneg i
      · intro i hi
        exact hlocalBound i

private theorem ghostChoiceCoeff_norm_mul_outputWeight_eq {K : ℕ}
    (F : PDFix K) (S : PDScale) (s : MemPoint S.x K) (B j : ℕ)
    (ρ v : ℝ) (choices : (i : Fin K) → GhostGroupChoice F s B i)
    (hη : 0 ≤ memoryEta S.x F.q_d j) (hq : 0 ≤ memoryQ S.x F.q_d j)
    (hV : ∀ i : Fin K, 0 ≤ bandMass S.x (F.a i)) (hρ : 0 < ρ) (hv : 0 < v)
    (hν : ∀ (i : Fin K) (k : Fin (choices i).2.1.1),
      0 ≤ memoryNu S.x K F.a F.q_d i ((choices i).2.2 k).1) :
    ‖((ghostChoiceCoeffReal F S s ρ j B choices : ℝ) : ℂ)‖ *
        v ^ memSize (ghostChoicesOutput F s B choices) =
      v ^ memSize s * ∏ i : Fin K, ghostGroupFiniteWeight F s B j ρ v i (choices i) := by
  classical
  let d (i : Fin K) := (choices i).1.1.card
  let l (i : Fin K) := (choices i).2.1.1
  let base := ∑ i : Fin K, ((s.2.2 i).length - d i)
  let ds := ∑ i : Fin K, d i
  let ls := ∑ i : Fin K, l i
  let rawNorm (i : Fin K) :=
    ‖((ghostGroupCoeff F S ρ j i (hitCount (s.2.2 i) s.1) (d i) (l i)
      (List.ofFn fun k => ((choices i).2.2 k).1) : ℝ) : ℂ)‖
  let weight (i : Fin K) := ghostGroupFiniteWeight F s B j ρ v i (choices i)
  have hd (i : Fin K) : d i ≤ (s.2.2 i).length := by
    dsimp [d]
    simpa using Finset.card_le_univ (choices i).1.1
  have hsource : memSize s = base + ds := by
    simp only [memSize]
    dsimp [base, ds]
    calc
      (∑ i : Fin K, (s.2.2 i).length) =
          ∑ i : Fin K, ((s.2.2 i).length - d i + d i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (Nat.sub_add_cancel (hd i)).symm
      _ = _ := by rw [Finset.sum_add_distrib]
  have htarget : memSize (ghostChoicesOutput F s B choices) = base + ls := by
    rw [ghostChoicesOutput_memSize]
    dsimp [base, ls, d, l]
    rw [Finset.sum_add_distrib]
  have hpowD : (∏ i : Fin K, v ^ d i) = v ^ ds := by
    simpa [ds] using
      (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin K)) d v)
  have hpowL : (∏ i : Fin K, v ^ l i) = v ^ ls := by
    simpa [ls] using
      (Finset.prod_pow_eq_pow_sum (Finset.univ : Finset (Fin K)) l v)
  have hnorm :
      ‖((ghostChoiceCoeffReal F S s ρ j B choices : ℝ) : ℂ)‖ =
        ∏ i : Fin K, rawNorm i := by
    simp [ghostChoiceCoeffReal, rawNorm, Complex.norm_real, Real.norm_eq_abs,
      Finset.abs_prod, d, l]
  have hlocal (i : Fin K) : weight i * v ^ d i = rawNorm i * v ^ l i := by
    dsimp [weight, rawNorm, d, l]
    apply ghostGroupFiniteWeight_mul_pow_eq_normCoeff_mul_pow
      F S s B j ρ v i (choices i) hη hq (hV i) hρ hv
    intro k
    exact hν i k
  have hweighted :
      (∏ i : Fin K, weight i) * v ^ ds =
        (∏ i : Fin K, rawNorm i) * v ^ ls := by
    calc
      _ = ∏ i : Fin K, weight i * v ^ d i := by
        rw [← hpowD, ← Finset.prod_mul_distrib]
      _ = ∏ i : Fin K, rawNorm i * v ^ l i := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hlocal i
      _ = _ := by rw [Finset.prod_mul_distrib, hpowL]
  calc
    _ = (∏ i : Fin K, rawNorm i) * v ^ (base + ls) := by rw [hnorm, htarget]
    _ = v ^ base * ((∏ i : Fin K, rawNorm i) * v ^ ls) := by rw [pow_add]; ring
    _ = v ^ base * ((∏ i : Fin K, weight i) * v ^ ds) := by rw [← hweighted]
    _ = v ^ (base + ds) * ∏ i : Fin K, weight i := by rw [pow_add]; ring
    _ = _ := by rw [← hsource]

private theorem memGhostProjected_rowSchur_le_of_params {K : ℕ}
    (F : PDFix K) (hF : F.Valid) (S : PDScale) (ρ : ℝ) (hρ : IsMemoryRho F.q_d ρ)
    (j B : ℕ) (v : ℝ) (hv : 0 < v)
    (hvlarge : 2 / (ρ * (1 - Real.sqrt F.q_d / ρ ^ 2)) ≤ v)
    (hV : ∀ i : Fin K, 0 < bandMass S.x (F.a i))
    (hbp : ∀ p ∈ markedPrimes S.x K F.a,
      (1 / 2 : ℝ) ≤ memoryBPrime S.x F.q_d p) :
    MemRowSchurLE_sym F S B (memGhost F S ρ j) v
      (∏ i : Fin K,
        Real.exp (2 * memoryEta S.x F.q_d j * bandMass S.x (F.a i) * v / ρ)) := by
  classical
  have hρsq : ρ ^ 2 < 1 := by nlinarith [hρ.1, hρ.2.1]
  have hqLt : memoryQ S.x F.q_d j < 1 := by
    unfold memoryQ
    split_ifs <;> [exact lt_trans hρ.2.2 hρsq; exact hF.2.2.1]
  have hη : 0 ≤ memoryEta S.x F.q_d j := by
    unfold memoryEta
    linarith [hqLt]
  have hq : 0 ≤ memoryQ S.x F.q_d j := by
    unfold memoryQ
    split_ifs
    · exact Real.sqrt_nonneg _
    · exact hF.2.1.le
  change MemRowSchurLE F S B
    (fun f => memGhost F S ρ j (memorySym f)) v
    (∏ i : Fin K,
      Real.exp (2 * memoryEta S.x F.q_d j * bandMass S.x (F.a i) * v / ρ))
  intro s hs hsSize T hT
  let choicesType := (i : Fin K) → GhostGroupChoice F s (2 * B) i
  have hν (choices : choicesType) (i : Fin K) (k : Fin (choices i).2.1.1) :
      0 ≤ memoryNu S.x K F.a F.q_d i ((choices i).2.2 k).1 := by
    let p := (choices i).2.2 k
    have hbpPos : 0 < memoryBPrime S.x F.q_d p.1 :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
        (hbp p.1 (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, p.2⟩))
    have hden : 0 < bandMass S.x (F.a i) * ((p.1 : ℝ) + 1) *
        memoryBPrime S.x F.q_d p.1 :=
      mul_pos (mul_pos (hV i) (by positivity)) hbpPos
    unfold memoryNu
    exact div_nonneg (by norm_num) hden.le
  have hrepr (t : MemPoint S.x K) (ht : t ∈ T) :
      memKernel (fun f => memGhost F S ρ j (memorySym f)) s t =
        ∑ choices : choicesType,
          ghostChoiceKernelTerm F S s t ρ j B choices := by
    exact memGhostProjectedKernel_choiceSum F S ρ j s t B hsSize
      (hT t ht)
  have hpoint (t : MemPoint S.x K) (ht : t ∈ T) :
      ‖memKernel (fun f => memGhost F S ρ j (memorySym f)) s t‖ ≤
        ∑ choices : choicesType, ‖ghostChoiceKernelTerm F S s t ρ j B choices‖ := by
    rw [hrepr t ht]
    exact norm_sum_le (Finset.univ : Finset choicesType)
      (fun choices => ghostChoiceKernelTerm F S s t ρ j B choices)
  have hrow :
      (∑ t ∈ T,
        ‖memKernel (fun f => memGhost F S ρ j (memorySym f)) s t‖ * v ^ memSize t) ≤
        ∑ choices : choicesType,
          ‖((ghostChoiceCoeffReal F S s ρ j (2 * B) choices : ℝ) : ℂ)‖ *
            v ^ memSize (ghostChoicesOutput F s (2 * B) choices) := by
    calc
      _ ≤ ∑ t ∈ T,
            (∑ choices : choicesType,
              ‖ghostChoiceKernelTerm F S s t ρ j B choices‖) * v ^ memSize t := by
        apply Finset.sum_le_sum
        intro t ht
        exact mul_le_mul_of_nonneg_right (hpoint t ht) (pow_nonneg hv.le _)
      _ = ∑ choices : choicesType,
            ∑ t ∈ T,
              ‖ghostChoiceKernelTerm F S s t ρ j B choices‖ * v ^ memSize t := by
        calc
          _ = ∑ t ∈ T,
                ∑ choices : choicesType,
                  ‖ghostChoiceKernelTerm F S s t ρ j B choices‖ * v ^ memSize t := by
            apply Finset.sum_congr rfl
            intro t ht
            simpa using (Finset.sum_mul (Finset.univ : Finset choicesType)
              (fun choices => ‖ghostChoiceKernelTerm F S s t ρ j B choices‖)
              (v ^ memSize t))
          _ = _ := by
            simpa using (Finset.sum_comm (s := T)
              (t := (Finset.univ : Finset choicesType))
              (f := fun t choices =>
                ‖ghostChoiceKernelTerm F S s t ρ j B choices‖ * v ^ memSize t))
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro choices hchoices
        exact ghostChoiceKernelTerm_row_sum_le F S s ρ j B choices v hv T
  have hrow' :
      (∑ choices : choicesType,
        ‖((ghostChoiceCoeffReal F S s ρ j (2 * B) choices : ℝ) : ℂ)‖ *
          v ^ memSize (ghostChoicesOutput F s (2 * B) choices)) =
        v ^ memSize s *
          ∑ choices : choicesType,
            ∏ i : Fin K, ghostGroupFiniteWeight F s (2 * B) j ρ v i (choices i) := by
    calc
      _ = ∑ choices : choicesType,
            v ^ memSize s *
              ∏ i : Fin K, ghostGroupFiniteWeight F s (2 * B) j ρ v i (choices i) := by
        apply Finset.sum_congr rfl
        intro choices hc
        exact ghostChoiceCoeff_norm_mul_outputWeight_eq F S s (2 * B) j ρ v choices
          hη hq (fun i => (hV i).le) hρ.1 hv (hν choices)
      _ = _ := by rw [Finset.mul_sum]
  calc
    _ ≤ v ^ memSize s *
          ∑ choices : choicesType,
            ∏ i : Fin K, ghostGroupFiniteWeight F s (2 * B) j ρ v i (choices i) := by
      rw [hrow'] at hrow
      exact hrow
    _ ≤ v ^ memSize s *
          ∏ i : Fin K,
            Real.exp (2 * memoryEta S.x F.q_d j * bandMass S.x (F.a i) * v / ρ) := by
      apply mul_le_mul_of_nonneg_left
        (ghost_all_group_choices_le_exp F hF s (2 * B) j ρ hρ v hv hvlarge hV hbp)
      exact pow_nonneg hv.le _
    _ = _ := by ring

private theorem bandMass_pos_of_large_x {K : ℕ} (F : PDFix K) (hF : F.Valid) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ i : Fin K,
      0 < bandMass x (F.a i) := by
  classical
  let x_i : Fin K → ℝ := fun i =>
    Classical.choose (band_mass (F.a i)
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 10) (hF.1.2.1 i).1)
      (lt_trans (hF.1.2.1 i).2 (by norm_num))
      (Real.log 2) (Real.log_pos (by norm_num)))
  have hx_i : ∀ i : Fin K,
      2 ≤ x_i i ∧ ∀ x : ℝ, x_i i ≤ x →
        |bandMass x (F.a i) - Real.log 2| ≤ Real.log 2 ∧
          0 < bandMass x (F.a i) := by
    intro i
    exact Classical.choose_spec (band_mass (F.a i)
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 10) (hF.1.2.1 i).1)
      (lt_trans (hF.1.2.1 i).2 (by norm_num))
      (Real.log 2) (Real.log_pos (by norm_num)))
  let x₀ : ℝ := 2 + ∑ i : Fin K, x_i i
  have hx₀ : 2 ≤ x₀ := by
    dsimp [x₀]
    have hsum : 0 ≤ ∑ i : Fin K, x_i i :=
      Finset.sum_nonneg fun i hi => by linarith [(hx_i i).1]
    linarith
  refine ⟨x₀, hx₀, ?_⟩
  intro x hx i
  have hsingle : x_i i ≤ ∑ j : Fin K, x_i j :=
    Finset.single_le_sum (s := Finset.univ) (f := x_i)
      (fun j hj => by linarith [(hx_i j).1]) (Finset.mem_univ i)
  have hxi : x_i i ≤ x₀ := by dsimp [x₀]; linarith
  exact ((hx_i i).2 x (le_trans hxi hx)).2

/-- `t2:pd.ghost-edge-crude` — PD 04:365-435.  REPLACES the frozen `ghost_edge_crude`.  On
`ℋ_B`, with the Schur weight `v₀^{k_tot}`: ghost row and column sums (mem:ghost-row),
(mem:ghost-column) are `≤ C_K` once `v₀` makes both parentheses `≤ 1` (uses `ρ² > √q_d`), so
`‖𝒢_j‖ ≤ C_K` (mem:ghost-norm); edge rows and columns are `≤ C_K B^K (1+L^{3A₀}) ≤ L^{C}`
(mem:edge-crude; columns via the adjoint rules, PD 04:310-348). Correction from refutation lane
`sol-gate-b` states these bounds after symmetric-memory projection. -/
theorem ghost_edge_crude (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ v₀ C_K Cexp x₀ : ℝ, 1 < v₀ ∧ 0 < C_K ∧ 0 < Cexp ∧ 2 ≤ x₀ ∧
        ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
          ∀ w : ArchRoot, w.InRegion S → ∀ j : ℕ, j ≤ S.N →
            MemRowSchurLE_sym F S (memoryCutoff S) (memGhost F S ρ j) v₀ C_K ∧
            MemColSchurLE_sym F S (memoryCutoff S) (memGhost F S ρ j) v₀ C_K ∧
            MemOpNormLE_sym F S (memoryCutoff S) (memGhost F S ρ j) C_K ∧
            (j < S.N →
              MemRowSchurLE_sym F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.full j) v₀
                (Real.rpow S.L Cexp) ∧
              MemColSchurLE_sym F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.full j) v₀
                  (Real.rpow S.L Cexp)) := by
  intro K F hF ρ hρ
  obtain ⟨xB, hxB, hBPrime⟩ := memoryBPrime_half_of_large_x F hF
  obtain ⟨xV, hxV, hBandMass⟩ := bandMass_le_two_log_two_of_large_x F hF
  obtain ⟨xPos, hxPos, hBandMassPos⟩ := bandMass_pos_of_large_x F hF
  let g := 1 - Real.sqrt F.q_d / ρ ^ 2
  have hρsqpos : 0 < ρ ^ 2 := sq_pos_of_pos hρ.1
  have hratio : Real.sqrt F.q_d / ρ ^ 2 < 1 :=
    (div_lt_one₀ hρsqpos).2 hρ.2.2
  have hg : 0 < g := by dsimp [g]; linarith
  let vbase := max 2 (2 / (ρ * g))
  let vscale := max 2 (2 * Real.log 2)
  let v₀ := vbase * vscale
  have hvbase2 : 2 ≤ vbase := le_max_left _ _
  have hvscale2 : 2 ≤ vscale := le_max_left _ _
  have hvbasepos : 0 ≤ vbase := by linarith
  have hvscale1 : 1 ≤ vscale := by linarith
  have hv₀ : 1 < v₀ := by
    have hproduct : 4 ≤ vbase * vscale := by
      calc
        4 = (2 : ℝ) * 2 := by norm_num
        _ ≤ vbase * 2 := mul_le_mul_of_nonneg_right hvbase2 (by norm_num)
        _ ≤ vbase * vscale := mul_le_mul_of_nonneg_left hvscale2 hvbasepos
    dsimp [v₀]
    linarith
  have hv₀pos : 0 < v₀ := by linarith
  have hv₀large : 2 / (ρ * (1 - Real.sqrt F.q_d / ρ ^ 2)) ≤ v₀ := by
    calc
      2 / (ρ * (1 - Real.sqrt F.q_d / ρ ^ 2)) = 2 / (ρ * g) := by rfl
      _ ≤ vbase := le_max_right _ _
      _ = vbase * 1 := by ring
      _ ≤ vbase * vscale := mul_le_mul_of_nonneg_left hvscale1 hvbasepos
      _ = v₀ := rfl
  let C_K := (Real.exp (4 * Real.log 2 * v₀ / ρ)) ^ K
  let Cexp : ℝ := 1
  let x₀ := max xB (max xV xPos)
  have hC_K : 0 < C_K := by
    dsimp [C_K]
    exact pow_pos (Real.exp_pos _) _
  have hCexp : 0 < Cexp := by norm_num [Cexp]
  have hx₀ : 2 ≤ x₀ := by
    dsimp [x₀]
    exact le_trans hxB (le_max_left _ _)
  have hηone (x : ℝ) (j : ℕ) : memoryEta x F.q_d j ≤ 1 := by
    have hqj : 0 ≤ memoryQ x F.q_d j := by
      unfold memoryQ
      split_ifs
      · exact Real.sqrt_nonneg _
      · exact hF.2.1.le
    unfold memoryEta
    linarith
  have hExpBound (S : PDScale) (hS : S.Valid K δ c₁ c₂) (hx : x₀ ≤ S.x)
      (j : ℕ) :
      (∏ i : Fin K,
        Real.exp (2 * memoryEta S.x F.q_d j * bandMass S.x (F.a i) * v₀ / ρ)) ≤ C_K := by
    have hxB' : xB ≤ S.x := (le_max_left _ _).trans hx
    have hxV' : xV ≤ S.x := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hx
    have hxPos' : xPos ≤ S.x :=
      (le_trans (le_max_right _ _) (le_max_right _ _)).trans hx
    have hmassPos (i : Fin K) : 0 < bandMass S.x (F.a i) :=
      hBandMassPos S.x hxPos' i
    have hmassLe (i : Fin K) : bandMass S.x (F.a i) ≤ 2 * Real.log 2 := by
      exact hBandMass S.x hxV' i
    have heta : memoryEta S.x F.q_d j ≤ 1 := hηone S.x j
    have hfac : 0 ≤ 2 * v₀ / ρ := div_nonneg (by positivity) hρ.1.le
    have hexpArg (i : Fin K) :
        2 * memoryEta S.x F.q_d j * bandMass S.x (F.a i) * v₀ / ρ ≤
          4 * Real.log 2 * v₀ / ρ := by
      have hηVraw := mul_le_mul_of_nonneg_right heta (hmassPos i).le
      have hηV : memoryEta S.x F.q_d j * bandMass S.x (F.a i) ≤
          bandMass S.x (F.a i) := by simpa using hηVraw
      have hV := mul_le_mul_of_nonneg_left (hmassLe i) hfac
      calc
        2 * memoryEta S.x F.q_d j * bandMass S.x (F.a i) * v₀ / ρ =
            (2 * v₀ / ρ) *
              (memoryEta S.x F.q_d j * bandMass S.x (F.a i)) := by ring
        _ ≤ (2 * v₀ / ρ) * bandMass S.x (F.a i) :=
          mul_le_mul_of_nonneg_left hηV hfac
        _ ≤ (2 * v₀ / ρ) * (2 * Real.log 2) := hV
        _ = 4 * Real.log 2 * v₀ / ρ := by ring
    calc
      _ ≤ ∏ i : Fin K, Real.exp (4 * Real.log 2 * v₀ / ρ) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          exact (Real.exp_pos _).le
        · intro i hi
          exact Real.exp_le_exp.mpr (hexpArg i)
      _ = C_K := by simp [C_K]
  have hrow (S : PDScale) (hS : S.Valid K δ c₁ c₂) (hx : x₀ ≤ S.x)
      (j : ℕ) :
      MemRowSchurLE_sym F S (memoryCutoff S) (memGhost F S ρ j) v₀ C_K := by
    have hxB' : xB ≤ S.x := (le_max_left _ _).trans hx
    have hxPos' : xPos ≤ S.x :=
      (le_trans (le_max_right _ _) (le_max_right _ _)).trans hx
    have hmass (i : Fin K) : 0 < bandMass S.x (F.a i) :=
      hBandMassPos S.x hxPos' i
    have hbp (p : ℕ) (hp : p ∈ markedPrimes S.x K F.a) :
        (1 / 2 : ℝ) ≤ memoryBPrime S.x F.q_d p := hBPrime S.x hxB' p hp
    have hparam := memGhostProjected_rowSchur_le_of_params F hF S ρ hρ j
      (memoryCutoff S) v₀ hv₀pos hv₀large hmass hbp
    change MemRowSchurLE F S (memoryCutoff S)
      (fun f => memGhost F S ρ j (memorySym f)) v₀ C_K
    intro s hs hsSize T hT
    calc
      _ ≤ (∏ i : Fin K,
          Real.exp (2 * memoryEta S.x F.q_d j * bandMass S.x (F.a i) * v₀ / ρ)) *
            v₀ ^ memSize s := hparam s hs hsSize T hT
      _ ≤ C_K * v₀ ^ memSize s :=
        mul_le_mul_of_nonneg_right (hExpBound S hS hx j) (pow_nonneg hv₀pos.le _)
  refine ⟨v₀, C_K, Cexp, x₀, hv₀, hC_K, hCexp, hx₀, ?_⟩
  intro S hS hx w hw j hj
  refine ⟨hrow S hS hx j, ?_⟩
  sorry

/-- `t2:pd.lattice-clean` (a) — PD 04:439-497.  Lattice box at a source passing good test (i):
in the coordinates `(h,l)` of `z' = h z + l D w_z`, the region `|l| ≤ C₁ Y`, `|h + lα| ≤ C₁`
(`α = D τ(w_z)/τ(z)`, from cell separation and the box) is covered, after a unimodular change of
coordinates, by a centered box with sides `A', B'`, `A'B' ≪ Y`, `Y^{0.1} ≤ A',B' ≤ Y^{0.9}`
(mem:lattice-shape).  Pure geometry of numbers: shortest vector `≥ Y^{-0.8}` by test (i),
`≪ Y^{-1/2}` by Dirichlet. -/
private def shearX (α : ℝ) (z : ℤ × ℤ) : ℝ := (z.1 : ℝ) + (z.2 : ℝ) * α

private def shearY (Y : ℝ) (z : ℤ × ℤ) : ℝ := (z.2 : ℝ) / Y

private def shearSize (Y α : ℝ) (z : ℤ × ℤ) : ℝ :=
  max |shearX α z| |shearY Y z|

private theorem circleDistance_le_abs_sub_int (t : ℝ) (z : ℤ) :
    circleDistance t ≤ |t - (z : ℝ)| := by
  unfold circleDistance
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro y ⟨k, rfl⟩
    exact abs_nonneg _
  · exact ⟨z, rfl⟩

private theorem exists_primitive_shear_vector (Y α : ℝ) (hY : 1 < Y)
    (hbad : ∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Real.rpow Y (1 / 5 : ℝ) →
      Real.rpow Y (-(7 / 10 : ℝ)) < circleDistance ((l : ℝ) * α)) :
    ∃ h l : ℤ, Int.gcd h l = 1 ∧
      Real.rpow Y (-(4 / 5 : ℝ)) ≤ shearSize Y α (h, l) ∧
      shearSize Y α (h, l) ≤ 2 / Real.sqrt Y := by
  classical
  have hYpos : 0 < Y := lt_trans zero_lt_one hY
  have hYone : 1 ≤ Y := hY.le
  let s : ℝ := Real.sqrt Y
  have hspos : 0 < s := by dsimp [s]; positivity
  have hsone : 1 ≤ s := by
    dsimp [s]
    exact (Real.one_le_sqrt).2 hYone
  let n : ℕ := ⌈s⌉₊
  have hsle : s ≤ (n : ℝ) := by
    dsimp [n]
    exact Nat.le_ceil _
  have hnpos : 0 < n := by
    have hcast : (1 : ℝ) ≤ (n : ℝ) := le_trans hsone hsle
    exact_mod_cast hcast
  obtain ⟨j, k, hkpos, hkn, happrox⟩ :=
    Real.exists_int_int_abs_mul_sub_le α (n := n) hnpos
  let h : ℤ := -j
  let l : ℤ := k
  have hlpos : 0 < l := by simpa [l] using hkpos
  have hfirst : |shearX α (h, l)| ≤ 1 / s := by
    have hnplus : s ≤ (n : ℝ) + 1 := by linarith [hsle]
    have hrecip : 1 / ((n : ℝ) + 1) ≤ 1 / s := by
      rw [div_le_div_iff₀ (by positivity) hspos]
      linarith
    have happrox' : |(k : ℝ) * α - j| ≤ 1 / ((n : ℝ) + 1) := by
      simpa only [Nat.cast_add, Nat.cast_one] using happrox
    calc
      |shearX α (h, l)| = |(k : ℝ) * α - j| := by
        simp [shearX, h, l, sub_eq_add_neg, add_comm]
      _ ≤ 1 / ((n : ℝ) + 1) := happrox'
      _ ≤ 1 / s := hrecip
  have hknCast : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
  have hsquare : s ^ 2 = Y := by dsimp [s]; exact Real.sq_sqrt hYpos.le
  have hsqrtLeY : s ≤ Y := by
    have hYsq : Y ≤ Y ^ 2 := by nlinarith [hY]
    dsimp [s]
    exact Real.sqrt_le_iff.mpr ⟨hYpos.le, hYsq⟩
  have hsecond : |shearY Y (h, l)| ≤ 2 / s := by
    have hkY : (k : ℝ) * s ≤ 2 * Y := by
      have hkn' : (k : ℝ) ≤ s + 1 := hknCast.trans_lt (Nat.ceil_lt_add_one (by positivity)) |>.le
      have hprod := mul_le_mul_of_nonneg_right hkn' hspos.le
      nlinarith [hprod, hsquare, hsqrtLeY]
    have hquot : (k : ℝ) / Y ≤ 2 / s := by
      rw [div_le_div_iff₀ hYpos hspos]
      exact hkY
    simpa [shearY, h, l, abs_of_pos (by positivity : 0 < (k : ℝ) / Y)] using hquot
  have hgpos : 0 < Int.gcd h l := Int.gcd_pos_of_ne_zero_right h hlpos.ne'
  obtain ⟨g, h', l', hg, hgcd, hh, hl⟩ := Int.exists_gcd_one' hgpos
  have hgcast : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hg)
  have hscaleX : shearX α (h, l) = (g : ℝ) * shearX α (h', l') := by
    dsimp [shearX]
    rw [hh, hl]
    push_cast
    ring
  have hscaleY : shearY Y (h, l) = (g : ℝ) * shearY Y (h', l') := by
    dsimp [shearY]
    rw [hl]
    push_cast
    ring
  have hgAbs : |(g : ℝ)| = (g : ℝ) := abs_of_nonneg (by positivity)
  have hxnorm : |shearX α (h', l')| ≤ |shearX α (h, l)| := by
    rw [hscaleX, abs_mul, hgAbs]
    nlinarith [mul_nonneg (sub_nonneg.mpr hgcast) (abs_nonneg (shearX α (h', l')))]
  have hynorm : |shearY Y (h', l')| ≤ |shearY Y (h, l)| := by
    rw [hscaleY, abs_mul, hgAbs]
    nlinarith [mul_nonneg (sub_nonneg.mpr hgcast) (abs_nonneg (shearY Y (h', l')))]
  refine ⟨h', l', hgcd, ?_, ?_⟩
  · by_contra hnot
    have hsmall : shearSize Y α (h', l') < Real.rpow Y (-(4 / 5 : ℝ)) := lt_of_not_ge hnot
    have hpowle : Real.rpow Y (-(4 / 5 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hYone (by norm_num)
    have hsizeone : shearSize Y α (h', l') < 1 := hsmall.trans_le hpowle
    by_cases hlzero : l' = 0
    · have hhsmall : |(h' : ℝ)| < 1 := by
        have hxle : |shearX α (h', l')| ≤ shearSize Y α (h', l') := le_max_left _ _
        simpa [shearX, hlzero] using lt_of_le_of_lt hxle hsizeone
      have hzcast : -1 < (h' : ℝ) ∧ (h' : ℝ) < 1 := abs_lt.mp hhsmall
      have hz : -1 < h' ∧ h' < 1 := by exact_mod_cast hzcast
      have hhzero : h' = 0 := by omega
      simp [hlzero, hhzero] at hgcd
    · have hmpos : 0 < l'.natAbs := Int.natAbs_pos.mpr hlzero
      have hmcast : (l'.natAbs : ℝ) = |(l' : ℝ)| := by
        have h := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs l')
        simpa using h
      have hcoord : |(l' : ℝ)| / Y ≤ shearSize Y α (h', l') := by
        calc
          |(l' : ℝ)| / Y = |shearY Y (h', l')| := by
            simp [shearY, abs_div, abs_of_pos hYpos]
          _ ≤ shearSize Y α (h', l') := le_max_right _ _
      have hsmallcoord : (l'.natAbs : ℝ) / Y < Real.rpow Y (-(4 / 5 : ℝ)) := by
        rw [hmcast]
        exact lt_of_le_of_lt hcoord hsmall
      have hprod : (l'.natAbs : ℝ) ≤ Real.rpow Y (-(4 / 5 : ℝ)) * Y :=
        (div_le_iff₀ hYpos).mp hsmallcoord.le
      have hpowmul : Real.rpow Y (-(4 / 5 : ℝ)) * Y = Real.rpow Y (1 / 5 : ℝ) := by
        calc
          Real.rpow Y (-(4 / 5 : ℝ)) * Y =
              Real.rpow Y (-(4 / 5 : ℝ)) * Real.rpow Y 1 := by
                exact congrArg (fun q : ℝ => Real.rpow Y (-(4 / 5 : ℝ)) * q)
                  (Real.rpow_one Y).symm
          _ = Real.rpow Y (-(4 / 5 : ℝ) + 1) :=
            (Real.rpow_add hYpos (-(4 / 5 : ℝ)) 1).symm
          _ = Real.rpow Y (1 / 5 : ℝ) := by congr 1 <;> norm_num
      have hmBound : (l'.natAbs : ℝ) ≤ Real.rpow Y (1 / 5 : ℝ) := by
        rw [hpowmul] at hprod
        exact hprod
      have hmone : 1 ≤ l'.natAbs := Nat.one_le_iff_ne_zero.mpr (by omega)
      have hdist : circleDistance ((l'.natAbs : ℝ) * α) ≤ |shearX α (h', l')| := by
        have hmcast' : (l'.natAbs : ℝ) = |(l' : ℝ)| := hmcast
        by_cases hlnonneg : 0 ≤ l'
        · have hmcast'' : (l'.natAbs : ℝ) = (l' : ℝ) := by
            rw [hmcast', abs_of_nonneg (by exact_mod_cast hlnonneg)]
          have heq : (l'.natAbs : ℝ) * α - (-(h' : ℝ)) = shearX α (h', l') := by
            simp [shearX, hmcast'']
            ring
          calc
            circleDistance ((l'.natAbs : ℝ) * α) ≤
                |(l'.natAbs : ℝ) * α - (-(h' : ℝ))| :=
                  by simpa only [Int.cast_neg] using circleDistance_le_abs_sub_int _ (-h')
            _ = |shearX α (h', l')| := by rw [heq]
        · have hlneg : (l' : ℝ) < 0 := by exact_mod_cast (lt_of_not_ge hlnonneg)
          have hmcast'' : (l'.natAbs : ℝ) = -(l' : ℝ) := by
            rw [hmcast', abs_of_neg hlneg]
          have heq : (l'.natAbs : ℝ) * α - (h' : ℝ) = -shearX α (h', l') := by
            simp [shearX, hmcast'']
            ring
          calc
            circleDistance ((l'.natAbs : ℝ) * α) ≤
                |(l'.natAbs : ℝ) * α - (h' : ℝ)| := circleDistance_le_abs_sub_int _ h'
            _ = |shearX α (h', l')| := by rw [heq, abs_neg]
      have htest := hbad l'.natAbs hmone hmBound
      have hxle : |shearX α (h', l')| ≤ shearSize Y α (h', l') := le_max_left _ _
      have hpowlt : Real.rpow Y (-(4 / 5 : ℝ)) < Real.rpow Y (-(7 / 10 : ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt hY (by norm_num)
      linarith
  · apply max_le
    · exact hxnorm.trans <| hfirst.trans <| by
        have hsplus : 1 / s ≤ 2 / s :=
          div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hspos.le
        exact hsplus
    · exact hynorm.trans hsecond

private def intDet (z z' : ℤ × ℤ) : ℤ := z.1 * z'.2 - z.2 * z'.1

private theorem shear_det (Y α : ℝ) (hY : 0 < Y) (z z' : ℤ × ℤ) :
    shearX α z * shearY Y z' - shearY Y z * shearX α z' =
      (intDet z z' : ℝ) / Y := by
  rcases z with ⟨h, l⟩
  rcases z' with ⟨h', l'⟩
  simp only [shearX, shearY, intDet]
  field_simp [hY.ne']
  push_cast
  ring

private theorem bound_det_second (Y lam x₁ y₁ x₂ y₂ : ℝ) (hY : 0 < Y) (hlam : 0 < lam)
    (hdet : x₁ * y₂ - y₁ * x₂ = 1 / Y) (hx₁ : |x₁| = lam) (hy₁ : |y₁| ≤ lam)
    (hx₂ : |x₂| ≤ lam / 2) (hlamsq : lam ^ 2 ≤ 4 / Y) :
    |y₂| ≤ 3 / (Y * lam) := by
  have hlamYsq : lam ^ 2 * Y ≤ 4 := by
    calc
      lam ^ 2 * Y ≤ (4 / Y) * Y := mul_le_mul_of_nonneg_right hlamsq hY.le
      _ = 4 := by field_simp [hY.ne']
  have hrel : x₁ * y₂ = 1 / Y + y₁ * x₂ := by linarith [hdet]
  have hprod : |x₁ * y₂| ≤ 3 / Y := by
    calc
      |x₁ * y₂| = |1 / Y + y₁ * x₂| := by rw [hrel]
      _ ≤ |1 / Y| + |y₁ * x₂| := abs_add_le _ _
      _ = 1 / Y + |y₁| * |x₂| := by rw [abs_of_pos (div_pos one_pos hY), abs_mul]
      _ ≤ 1 / Y + lam * (lam / 2) := by
        gcongr
      _ ≤ 3 / Y := by
        have hsum : 1 / Y + lam ^ 2 / 2 ≤ 3 / Y := by
          rw [le_div_iff₀ hY]
          field_simp [hY.ne']
          nlinarith [hlamYsq]
        nlinarith
  have habs : |y₂| = |x₁ * y₂| / lam := by
    rw [abs_mul, hx₁]
    field_simp [hlam.ne']
  rw [habs]
  calc
    |x₁ * y₂| / lam ≤ (3 / Y) / lam := div_le_div_of_nonneg_right hprod hlam.le
    _ = 3 / (Y * lam) := by field_simp [hY.ne', hlam.ne']

private theorem exists_shear_complement (Y α : ℝ) (z : ℤ × ℤ) (hY : 0 < Y)
    (hprim : Int.gcd z.1 z.2 = 1) (hlampos : 0 < shearSize Y α z)
    (hlamsq : shearSize Y α z ^ 2 ≤ 4 / Y) :
    ∃ z' : ℤ × ℤ, intDet z z' = 1 ∧
      shearSize Y α z' ≤ 3 / (Y * shearSize Y α z) := by
  classical
  let lam : ℝ := shearSize Y α z
  let zbase : ℤ × ℤ := (-Int.gcdB z.1 z.2, Int.gcdA z.1 z.2)
  have hlam : 0 < lam := hlampos
  have hlamsq' : lam ^ 2 ≤ 4 / Y := hlamsq
  have hlamYsq : lam ^ 2 * Y ≤ 4 := by
    calc
      lam ^ 2 * Y ≤ (4 / Y) * Y := mul_le_mul_of_nonneg_right hlamsq' hY.le
      _ = 4 := by field_simp [hY.ne']
  have hlamhalf : lam / 2 ≤ 3 / (Y * lam) := by
    rw [le_div_iff₀ (mul_pos hY hlam)]
    field_simp [hY.ne', hlam.ne']
    nlinarith [hlamYsq]
  have hBez : (Int.gcd z.1 z.2 : ℤ) = z.1 * Int.gcdA z.1 z.2 +
      z.2 * Int.gcdB z.1 z.2 := Int.gcd_eq_gcd_ab _ _
  have hzbase : intDet z zbase = 1 := by
    dsimp [intDet, zbase]
    rw [hprim] at hBez
    calc
      z.1 * Int.gcdA z.1 z.2 - z.2 * -Int.gcdB z.1 z.2 =
          z.1 * Int.gcdA z.1 z.2 + z.2 * Int.gcdB z.1 z.2 := by ring
      _ = 1 := hBez.symm
  let x₁ : ℝ := shearX α z
  let y₁ : ℝ := shearY Y z
  let x₂ : ℝ := shearX α zbase
  let y₂ : ℝ := shearY Y zbase
  by_cases hdom : |x₁| ≥ |y₁|
  · have hx₁ : |x₁| = lam := by
      dsimp [lam, shearSize, x₁, y₁]
      rw [max_eq_left hdom]
    have hy₁ : |y₁| ≤ lam := by
      dsimp [lam, shearSize, x₁, y₁]
      exact le_max_right _ _
    have hx₁ne : x₁ ≠ 0 := abs_ne_zero.mp (by rw [hx₁]; exact hlam.ne')
    let n : ℤ := round (x₂ / x₁)
    let z' : ℤ × ℤ := (zbase.1 - n * z.1, zbase.2 - n * z.2)
    have hz' : intDet z z' = 1 := by
      have hshift : intDet z (zbase.1 - n * z.1, zbase.2 - n * z.2) = intDet z zbase := by
        dsimp [intDet]
        ring
      simpa [z'] using hshift.trans hzbase
    have hx₂' : shearX α z' = x₂ - (n : ℝ) * x₁ := by
      dsimp [shearX, z', x₁, x₂]
      push_cast
      ring
    have hy₂' : shearY Y z' = y₂ - (n : ℝ) * y₁ := by
      dsimp [shearY, z', y₁, y₂]
      push_cast
      ring
    have hround : |x₂ / x₁ - (n : ℝ)| ≤ 1 / 2 := by
      dsimp [n]
      exact abs_sub_round _
    have hrel : x₂ - (n : ℝ) * x₁ = x₁ * (x₂ / x₁ - (n : ℝ)) := by
      field_simp [hx₁ne]
    have hround' : |x₂ / x₁ - (n : ℝ)| ≤ (2 : ℝ)⁻¹ := by
      convert hround using 1 <;> norm_num
    have hx₂small : |shearX α z'| ≤ lam / 2 := by
      rw [hx₂', hrel, abs_mul, hx₁]
      exact mul_le_mul_of_nonneg_left hround' hlam.le
    have hdet : x₁ * y₂ - y₁ * x₂ = 1 / Y := by
      have h := shear_det Y α hY z zbase
      have hdetCast : (intDet z zbase : ℝ) = 1 := by exact_mod_cast hzbase
      change x₁ * y₂ - y₁ * x₂ = (intDet z zbase : ℝ) / Y at h
      rw [hdetCast] at h
      simpa [x₁, y₁, x₂, y₂] using h
    have hdet' : x₁ * shearY Y z' - y₁ * shearX α z' = 1 / Y := by
      have h := shear_det Y α hY z z'
      have hdetCast : (intDet z z' : ℝ) = 1 := by exact_mod_cast hz'
      change x₁ * shearY Y z' - y₁ * shearX α z' = (intDet z z' : ℝ) / Y at h
      rw [hdetCast] at h
      simpa using h
    have hy₂bound := bound_det_second Y lam x₁ y₁ (shearX α z') (shearY Y z')
      hY hlam hdet' hx₁ hy₁ hx₂small hlamsq'
    refine ⟨z', hz', ?_⟩
    dsimp [shearSize]
    exact max_le (hx₂small.trans hlamhalf) hy₂bound
  · have hdom' : |y₁| ≥ |x₁| := le_of_not_ge hdom
    have hy₁eq : |y₁| = lam := by
      dsimp [lam, shearSize, x₁, y₁]
      rw [max_eq_right hdom']
    have hx₁le : |x₁| ≤ lam := by
      dsimp [lam, shearSize, x₁, y₁]
      exact le_max_left _ _
    have hy₁ne : y₁ ≠ 0 := abs_ne_zero.mp (by rw [hy₁eq]; exact hlam.ne')
    let n : ℤ := round (y₂ / y₁)
    let z' : ℤ × ℤ := (zbase.1 - n * z.1, zbase.2 - n * z.2)
    have hz' : intDet z z' = 1 := by
      have hshift : intDet z (zbase.1 - n * z.1, zbase.2 - n * z.2) = intDet z zbase := by
        dsimp [intDet]
        ring
      simpa [z'] using hshift.trans hzbase
    have hx₂' : shearX α z' = x₂ - (n : ℝ) * x₁ := by
      dsimp [shearX, z', x₁, x₂]
      push_cast
      ring
    have hy₂' : shearY Y z' = y₂ - (n : ℝ) * y₁ := by
      dsimp [shearY, z', y₁, y₂]
      push_cast
      ring
    have hround : |y₂ / y₁ - (n : ℝ)| ≤ 1 / 2 := by
      dsimp [n]
      exact abs_sub_round _
    have hrel : y₂ - (n : ℝ) * y₁ = y₁ * (y₂ / y₁ - (n : ℝ)) := by
      field_simp [hy₁ne]
    have hround' : |y₂ / y₁ - (n : ℝ)| ≤ (2 : ℝ)⁻¹ := by
      convert hround using 1 <;> norm_num
    have hy₂small : |shearY Y z'| ≤ lam / 2 := by
      rw [hy₂', hrel, abs_mul, hy₁eq]
      exact mul_le_mul_of_nonneg_left hround' hlam.le
    have hdet : x₁ * y₂ - y₁ * x₂ = 1 / Y := by
      have h := shear_det Y α hY z zbase
      have hdetCast : (intDet z zbase : ℝ) = 1 := by exact_mod_cast hzbase
      change x₁ * y₂ - y₁ * x₂ = (intDet z zbase : ℝ) / Y at h
      rw [hdetCast] at h
      simpa [x₁, y₁, x₂, y₂] using h
    have hdet' : y₁ * (-shearX α z') - x₁ * (-shearY Y z') = 1 / Y := by
      have h := shear_det Y α hY z z'
      have hdetCast : (intDet z z' : ℝ) = 1 := by exact_mod_cast hz'
      change x₁ * shearY Y z' - y₁ * shearX α z' = (intDet z z' : ℝ) / Y at h
      rw [hdetCast] at h
      nlinarith [h]
    have hx₂bound := bound_det_second Y lam y₁ x₁ (-shearY Y z') (-shearX α z')
      hY hlam hdet' hy₁eq hx₁le (by simpa [abs_neg] using hy₂small) hlamsq'
    refine ⟨z', hz', ?_⟩
    dsimp [shearSize]
    have hx₂small : |shearX α z'| ≤ 3 / (Y * lam) := by simpa [abs_neg] using hx₂bound
    have hy₂bound : |shearY Y z'| ≤ 3 / (Y * lam) := hy₂small.trans hlamhalf
    exact max_le hx₂small hy₂bound

set_option maxHeartbeats 500000 in
theorem lattice_shape (C₁ : ℝ) (hC₁ : 1 ≤ C₁) :
    ∃ C₂ Y₀ : ℝ, 0 < C₂ ∧ 1 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y → ∀ α : ℝ,
      (∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Real.rpow Y (1 / 5 : ℝ) →
        Real.rpow Y (-(7 / 10 : ℝ)) < circleDistance ((l : ℝ) * α)) →
      ∃ (a₀ b₀ c₀ d₀ : ℤ) (A' B' : ℝ), a₀ * d₀ - b₀ * c₀ = 1 ∧ A' * B' ≤ C₂ * Y ∧
        Real.rpow Y (1 / 10 : ℝ) ≤ A' ∧ A' ≤ Real.rpow Y (9 / 10 : ℝ) ∧
        Real.rpow Y (1 / 10 : ℝ) ≤ B' ∧ B' ≤ Real.rpow Y (9 / 10 : ℝ) ∧
        ∀ h l : ℤ, |(l : ℝ)| ≤ C₁ * Y → |(h : ℝ) + (l : ℝ) * α| ≤ C₁ →
          |((d₀ * h - b₀ * l : ℤ) : ℝ)| ≤ A' ∧ |((a₀ * l - c₀ * h : ℤ) : ℝ)| ≤ B' := by
  let C₂ : ℝ := 12 * C₁ ^ 2
  let Y₀ : ℝ := (8 * C₁) ^ 10
  have hC₂pos : 0 < C₂ := by dsimp [C₂]; positivity
  have h8C : 1 ≤ 8 * C₁ := by nlinarith [hC₁]
  have hY₀one : 1 ≤ Y₀ := by dsimp [Y₀]; exact one_le_pow₀ h8C
  refine ⟨C₂, Y₀, hC₂pos, hY₀one, ?_⟩
  intro Y hY α hbad
  have h8Cgt : 1 < 8 * C₁ := by nlinarith [hC₁]
  have hY₀gt : 1 < Y₀ := by
    dsimp [Y₀]
    have hpow : (1 : ℝ) ^ 10 < (8 * C₁) ^ 10 := by gcongr
    simpa using hpow
  have hYgt : 1 < Y := lt_of_lt_of_le hY₀gt hY
  have hYpos : 0 < Y := lt_trans zero_lt_one hYgt
  have hYone : 1 ≤ Y := hYgt.le
  have hBasePow : (8 * C₁) ^ 10 ≤ Y := by simpa [Y₀] using hY
  have hRootEq : Real.rpow ((8 * C₁) ^ 10) (1 / 10 : ℝ) = 8 * C₁ := by
    simpa [one_div] using
      (Real.pow_rpow_inv_natCast (by positivity : 0 ≤ 8 * C₁) (by norm_num : 10 ≠ 0))
  have hRoot : 8 * C₁ ≤ Real.rpow Y (1 / 10 : ℝ) := by
    calc
      8 * C₁ = Real.rpow ((8 * C₁) ^ 10) (1 / 10 : ℝ) := hRootEq.symm
      _ ≤ Real.rpow Y (1 / 10 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hBasePow (by norm_num)
  have hRoot4 : 8 * C₁ ≤ Real.rpow Y (2 / 5 : ℝ) := by
    exact hRoot.trans <| Real.rpow_le_rpow_of_exponent_le hYone (by norm_num)
  obtain ⟨a, c, hprim, hLamLow, hLamUp⟩ := exists_primitive_shear_vector Y α hYgt hbad
  let z₁ : ℤ × ℤ := (a, c)
  let lam : ℝ := shearSize Y α z₁
  have hLamPos : 0 < lam := by
    dsimp [lam, z₁]
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos hYpos _) hLamLow
  have hLamsq : lam ^ 2 ≤ 4 / Y := by
    have hdiff : 0 ≤ 2 / Real.sqrt Y - lam := sub_nonneg.mpr (by simpa [lam, z₁] using hLamUp)
    have hsum : 0 ≤ 2 / Real.sqrt Y + lam := by positivity
    have hsq : lam ^ 2 ≤ (2 / Real.sqrt Y) ^ 2 := by
      nlinarith [mul_nonneg hdiff hsum]
    have hsquare : (Real.sqrt Y) ^ 2 = Y := Real.sq_sqrt hYpos.le
    have hsqrtNe : Real.sqrt Y ≠ 0 := (Real.sqrt_ne_zero').2 hYpos
    have hdiv : (2 / Real.sqrt Y) ^ 2 = 4 / Y := by
      field_simp [hsqrtNe, hYpos.ne']
      rw [hsquare]
      ring
    rw [hdiv] at hsq
    exact hsq
  obtain ⟨z₂, hdetZ, hZ₂size⟩ := exists_shear_complement Y α z₁ hYpos hprim
    (by simpa [lam] using hLamPos) (by simpa [lam] using hLamsq)
  have hZ₂coords : |shearX α z₂| ≤ 3 / (Y * lam) ∧
      |shearY Y z₂| ≤ 3 / (Y * lam) := by
    simpa [shearSize, lam] using hZ₂size
  let a₀ : ℤ := z₁.1
  let c₀ : ℤ := z₁.2
  let b₀ : ℤ := z₂.1
  let d₀ : ℤ := z₂.2
  let A' : ℝ := 6 * C₁ / lam
  let B' : ℝ := 2 * C₁ * Y * lam
  have hdetFinal : a₀ * d₀ - b₀ * c₀ = 1 := by
    have h := hdetZ
    simpa [intDet, a₀, b₀, c₀, d₀, z₁, mul_comm] using h
  have hProductEq : A' * B' = C₂ * Y := by
    dsimp [A', B', C₂]
    field_simp [hLamPos.ne']
    ring
  have hSqrtEq : Real.sqrt Y = Real.rpow Y (1 / 2 : ℝ) := Real.sqrt_eq_rpow Y
  have hNegSqrt : (Real.sqrt Y)⁻¹ = Real.rpow Y (-(1 / 2 : ℝ)) := by
    calc
      (Real.sqrt Y)⁻¹ = (Real.rpow Y (1 / 2 : ℝ))⁻¹ := by rw [hSqrtEq]
      _ = Real.rpow Y (-(1 / 2 : ℝ)) := (Real.rpow_neg hYpos.le (1 / 2 : ℝ)).symm
  have hLamUpper : lam ≤ 2 * Real.rpow Y (-(1 / 2 : ℝ)) := by
    calc
      lam ≤ 2 / Real.sqrt Y := by simpa [lam, z₁] using hLamUp
      _ = 2 * (Real.sqrt Y)⁻¹ := by ring
      _ = 2 * Real.rpow Y (-(1 / 2 : ℝ)) := by rw [hNegSqrt]
  have hPowMul (u v : ℝ) :
      Real.rpow Y u * Real.rpow Y v = Real.rpow Y (u + v) :=
    (Real.rpow_add hYpos u v).symm
  have hPowA : Real.rpow Y (9 / 10 : ℝ) * Real.rpow Y (-(4 / 5 : ℝ)) =
      Real.rpow Y (1 / 10 : ℝ) := by
    convert hPowMul (9 / 10 : ℝ) (-(4 / 5 : ℝ)) using 1 <;> norm_num
  have hPowTiny : Real.rpow Y (1 / 10 : ℝ) * Real.rpow Y (-(1 / 2 : ℝ)) =
      Real.rpow Y (-(2 / 5 : ℝ)) := by
    convert hPowMul (1 / 10 : ℝ) (-(1 / 2 : ℝ)) using 1 <;> norm_num
  have hPowB : Real.rpow Y (1 : ℝ) * Real.rpow Y (-(4 / 5 : ℝ)) =
      Real.rpow Y (1 / 5 : ℝ) := by
    convert hPowMul (1 : ℝ) (-(4 / 5 : ℝ)) using 1 <;> norm_num
  have hPowS : Real.rpow Y (2 / 5 : ℝ) * Real.rpow Y (1 / 2 : ℝ) =
      Real.rpow Y (9 / 10 : ℝ) := by
    convert hPowMul (2 / 5 : ℝ) (1 / 2 : ℝ) using 1 <;> norm_num
  have hNegLeOne : Real.rpow Y (-(2 / 5 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hYone (by norm_num)
  have hAUpper : A' ≤ Real.rpow Y (9 / 10 : ℝ) := by
    dsimp [A']
    apply (div_le_iff₀ hLamPos).2
    calc
      6 * C₁ ≤ Real.rpow Y (1 / 10 : ℝ) := by nlinarith [hRoot]
      _ = Real.rpow Y (9 / 10 : ℝ) * Real.rpow Y (-(4 / 5 : ℝ)) := hPowA.symm
      _ ≤ Real.rpow Y (9 / 10 : ℝ) * lam :=
        mul_le_mul_of_nonneg_left hLamLow (Real.rpow_pos_of_pos hYpos _).le
  have hALower : Real.rpow Y (1 / 10 : ℝ) ≤ A' := by
    dsimp [A']
    apply (le_div_iff₀ hLamPos).2
    have hprod : Real.rpow Y (1 / 10 : ℝ) * lam ≤ 2 := by
      calc
        Real.rpow Y (1 / 10 : ℝ) * lam ≤
            Real.rpow Y (1 / 10 : ℝ) * (2 * Real.rpow Y (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hLamUpper (Real.rpow_pos_of_pos hYpos _).le
        _ = 2 * Real.rpow Y (-(2 / 5 : ℝ)) := by
          calc
            _ = 2 * (Real.rpow Y (1 / 10 : ℝ) * Real.rpow Y (-(1 / 2 : ℝ))) := by ring
            _ = 2 * Real.rpow Y (-(2 / 5 : ℝ)) := by rw [hPowTiny]
        _ ≤ 2 := by nlinarith [hNegLeOne]
    have hsmall : 2 ≤ 6 * C₁ := by nlinarith [hC₁]
    exact hprod.trans hsmall
  have hYlam : Real.rpow Y (1 / 5 : ℝ) ≤ Y * lam := by
    calc
      Real.rpow Y (1 / 5 : ℝ) = Real.rpow Y 1 * Real.rpow Y (-(4 / 5 : ℝ)) := hPowB.symm
      _ = Y * Real.rpow Y (-(4 / 5 : ℝ)) := by
        exact congrArg (fun x : ℝ => x * Real.rpow Y (-(4 / 5 : ℝ))) (Real.rpow_one Y)
      _ ≤ Y * lam := mul_le_mul_of_nonneg_left hLamLow hYpos.le
  have hBLower : Real.rpow Y (1 / 10 : ℝ) ≤ B' := by
    dsimp [B']
    calc
      Real.rpow Y (1 / 10 : ℝ) ≤ Real.rpow Y (1 / 5 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hYone (by norm_num)
      _ ≤ 2 * C₁ * Real.rpow Y (1 / 5 : ℝ) := by
        have hcoef : 0 ≤ 2 * C₁ - 1 := by nlinarith [hC₁]
        have hpow : 0 ≤ Real.rpow Y (1 / 5 : ℝ) :=
          (Real.rpow_pos_of_pos hYpos (1 / 5 : ℝ)).le
        have hmul : 0 ≤ (2 * C₁ - 1) * Real.rpow Y (1 / 5 : ℝ) := mul_nonneg hcoef hpow
        nlinarith [hmul]
      _ ≤ 2 * C₁ * (Y * lam) :=
        mul_le_mul_of_nonneg_left hYlam (by positivity)
      _ = 2 * C₁ * Y * lam := by ring
  have hBUpper : B' ≤ Real.rpow Y (9 / 10 : ℝ) := by
    dsimp [B']
    have hYmulNeg : Y * Real.rpow Y (-(1 / 2 : ℝ)) = Real.rpow Y (1 / 2 : ℝ) := by
      calc
      Y * Real.rpow Y (-(1 / 2 : ℝ)) =
            Real.rpow Y 1 * Real.rpow Y (-(1 / 2 : ℝ)) := by
              exact congrArg (fun x : ℝ => x * Real.rpow Y (-(1 / 2 : ℝ))) (Real.rpow_one Y).symm
        _ = Real.rpow Y (1 / 2 : ℝ) := by
          convert hPowMul (1 : ℝ) (-(1 / 2 : ℝ)) using 1 <;> norm_num
    calc
      2 * C₁ * Y * lam ≤ 2 * C₁ * Y * (2 * Real.rpow Y (-(1 / 2 : ℝ))) := by
        have hmul := mul_le_mul_of_nonneg_left hLamUpper (by positivity : 0 ≤ 2 * C₁ * Y)
        calc
          2 * C₁ * Y * lam = (2 * C₁ * Y) * lam := by ring
          _ ≤ (2 * C₁ * Y) * (2 * Real.rpow Y (-(1 / 2 : ℝ))) := hmul
          _ = 2 * C₁ * Y * (2 * Real.rpow Y (-(1 / 2 : ℝ))) := by ring
      _ = 4 * C₁ * Real.rpow Y (1 / 2 : ℝ) := by
        calc
          2 * C₁ * Y * (2 * Real.rpow Y (-(1 / 2 : ℝ))) =
              4 * C₁ * (Y * Real.rpow Y (-(1 / 2 : ℝ))) := by ring
          _ = 4 * C₁ * Real.rpow Y (1 / 2 : ℝ) := by rw [hYmulNeg]
      _ ≤ Real.rpow Y (2 / 5 : ℝ) * Real.rpow Y (1 / 2 : ℝ) := by
        have h4C : 4 * C₁ ≤ Real.rpow Y (2 / 5 : ℝ) := by linarith [hRoot4, hC₁]
        exact mul_le_mul_of_nonneg_right h4C (Real.rpow_pos_of_pos hYpos (1 / 2 : ℝ)).le
      _ = Real.rpow Y (9 / 10 : ℝ) := hPowS
  have hdetShear : shearX α z₁ * shearY Y z₂ - shearY Y z₁ * shearX α z₂ = 1 / Y := by
    have h := shear_det Y α hYpos z₁ z₂
    have hdetCast : (intDet z₁ z₂ : ℝ) = 1 := by exact_mod_cast hdetZ
    change shearX α z₁ * shearY Y z₂ - shearY Y z₁ * shearX α z₂ =
      (intDet z₁ z₂ : ℝ) / Y at h
    rw [hdetCast] at h
    exact h
  have hZ₁coords : |shearX α z₁| ≤ lam ∧ |shearY Y z₁| ≤ lam := by
    dsimp [lam, shearSize]
    exact ⟨le_max_left _ _, le_max_right _ _⟩
  have hBox : ∀ h l : ℤ, |(l : ℝ)| ≤ C₁ * Y →
      |(h : ℝ) + (l : ℝ) * α| ≤ C₁ →
        |((d₀ * h - b₀ * l : ℤ) : ℝ)| ≤ A' ∧
          |((a₀ * l - c₀ * h : ℤ) : ℝ)| ≤ B' := by
    intro h l hlBound hhBound
    let ξ : ℤ := d₀ * h - b₀ * l
    let η : ℤ := a₀ * l - c₀ * h
    have hcoordH : a₀ * ξ + b₀ * η = h := by
      dsimp [ξ, η]
      linear_combination h * hdetFinal
    have hcoordL : c₀ * ξ + d₀ * η = l := by
      dsimp [ξ, η]
      linear_combination l * hdetFinal
    have hcoordH' : (a₀ : ℝ) * (ξ : ℝ) + (b₀ : ℝ) * (η : ℝ) = (h : ℝ) := by
      exact_mod_cast hcoordH
    have hcoordL' : (c₀ : ℝ) * (ξ : ℝ) + (d₀ : ℝ) * (η : ℝ) = (l : ℝ) := by
      exact_mod_cast hcoordL
    have hXdecomp : shearX α (h, l) =
        (ξ : ℝ) * shearX α z₁ + (η : ℝ) * shearX α z₂ := by
      change (h : ℝ) + (l : ℝ) * α =
        (ξ : ℝ) * ((a₀ : ℝ) + (c₀ : ℝ) * α) +
          (η : ℝ) * ((b₀ : ℝ) + (d₀ : ℝ) * α)
      rw [← hcoordH', ← hcoordL']
      ring
    have hYdecomp : shearY Y (h, l) =
        (ξ : ℝ) * shearY Y z₁ + (η : ℝ) * shearY Y z₂ := by
      change (l : ℝ) / Y =
        (ξ : ℝ) * ((c₀ : ℝ) / Y) + (η : ℝ) * ((d₀ : ℝ) / Y)
      rw [← hcoordL']
      ring
    have hξFormula : (ξ : ℝ) = Y *
        (shearX α (h, l) * shearY Y z₂ - shearY Y (h, l) * shearX α z₂) := by
      rw [hXdecomp, hYdecomp]
      have hlin :
          ((ξ : ℝ) * shearX α z₁ + (η : ℝ) * shearX α z₂) * shearY Y z₂ -
          ((ξ : ℝ) * shearY Y z₁ + (η : ℝ) * shearY Y z₂) * shearX α z₂ =
            (ξ : ℝ) * (shearX α z₁ * shearY Y z₂ - shearY Y z₁ * shearX α z₂) := by ring
      rw [hlin, hdetShear]
      field_simp [hYpos.ne']
    have hηFormula : (η : ℝ) = Y *
        (shearX α z₁ * shearY Y (h, l) - shearY Y z₁ * shearX α (h, l)) := by
      rw [hXdecomp, hYdecomp]
      have hlin :
          shearX α z₁ * ((ξ : ℝ) * shearY Y z₁ + (η : ℝ) * shearY Y z₂) -
          shearY Y z₁ * ((ξ : ℝ) * shearX α z₁ + (η : ℝ) * shearX α z₂) =
            (η : ℝ) * (shearX α z₁ * shearY Y z₂ - shearY Y z₁ * shearX α z₂) := by ring
      rw [hlin, hdetShear]
      field_simp [hYpos.ne']
    have hTargetX : |shearX α (h, l)| ≤ C₁ := by simpa [shearX] using hhBound
    have hC₁nonneg : 0 ≤ C₁ := le_trans (by norm_num : (0 : ℝ) ≤ 1) hC₁
    have hTargetY : |shearY Y (h, l)| ≤ C₁ := by
      change |(l : ℝ) / Y| ≤ C₁
      rw [abs_div, abs_of_pos hYpos]
      exact (div_le_iff₀ hYpos).2 hlBound
    have hDetX : |shearX α (h, l) * shearY Y z₂ -
        shearY Y (h, l) * shearX α z₂| ≤
          C₁ * |shearY Y z₂| + C₁ * |shearX α z₂| := by
      calc
        _ ≤ |shearX α (h, l) * shearY Y z₂| +
            |shearY Y (h, l) * shearX α z₂| := by
          simpa using abs_sub_le (shearX α (h, l) * shearY Y z₂) 0
            (shearY Y (h, l) * shearX α z₂)
        _ = |shearX α (h, l)| * |shearY Y z₂| +
            |shearY Y (h, l)| * |shearX α z₂| := by rw [abs_mul, abs_mul]
        _ ≤ C₁ * |shearY Y z₂| + C₁ * |shearX α z₂| := by
            gcongr
    have hDetY : |shearX α z₁ * shearY Y (h, l) -
        shearY Y z₁ * shearX α (h, l)| ≤
          |shearX α z₁| * C₁ + |shearY Y z₁| * C₁ := by
      calc
        _ ≤ |shearX α z₁ * shearY Y (h, l)| +
            |shearY Y z₁ * shearX α (h, l)| := by
          simpa using abs_sub_le (shearX α z₁ * shearY Y (h, l)) 0
            (shearY Y z₁ * shearX α (h, l))
        _ = |shearX α z₁| * |shearY Y (h, l)| +
            |shearY Y z₁| * |shearX α (h, l)| := by rw [abs_mul, abs_mul]
        _ ≤ |shearX α z₁| * C₁ + |shearY Y z₁| * C₁ := by
            gcongr
    have hξBound : |(ξ : ℝ)| ≤ A' := by
      rw [hξFormula, abs_mul, abs_of_pos hYpos]
      calc
        Y * |shearX α (h, l) * shearY Y z₂ -
            shearY Y (h, l) * shearX α z₂| ≤
            Y * (C₁ * |shearY Y z₂| + C₁ * |shearX α z₂|) :=
          mul_le_mul_of_nonneg_left hDetX hYpos.le
        _ ≤ Y * (C₁ * (3 / (Y * lam)) + C₁ * (3 / (Y * lam))) := by
          apply mul_le_mul_of_nonneg_left
          · exact add_le_add
              (mul_le_mul_of_nonneg_left hZ₂coords.2 hC₁nonneg)
              (mul_le_mul_of_nonneg_left hZ₂coords.1 hC₁nonneg)
          · exact hYpos.le
        _ = A' := by dsimp [A']; field_simp [hYpos.ne', hLamPos.ne']; ring
    have hηBound : |(η : ℝ)| ≤ B' := by
      rw [hηFormula, abs_mul, abs_of_pos hYpos]
      calc
        Y * |shearX α z₁ * shearY Y (h, l) -
            shearY Y z₁ * shearX α (h, l)| ≤
            Y * (|shearX α z₁| * C₁ + |shearY Y z₁| * C₁) :=
          mul_le_mul_of_nonneg_left hDetY hYpos.le
        _ ≤ Y * (lam * C₁ + lam * C₁) := by
          apply mul_le_mul_of_nonneg_left
          · exact add_le_add
              (mul_le_mul_of_nonneg_right hZ₁coords.1 hC₁nonneg)
              (mul_le_mul_of_nonneg_right hZ₁coords.2 hC₁nonneg)
          · exact hYpos.le
        _ = B' := by dsimp [B']; ring
    exact ⟨by simpa [ξ] using hξBound, by simpa [η] using hηBound⟩
  have hproduct : A' * B' ≤ C₂ * Y := by
    exact hProductEq.le
  exact ⟨a₀, b₀, c₀, d₀, A', B', hdetFinal, hproduct,
    hALower, hAUpper, hBLower, hBUpper, hBox⟩

/-- `t2:pd.lattice-clean` (b) — PD 04:499-603.  REPLACES the frozen `lattice_clean`.  For every
`G` there is `A₀` with `‖ℰ_j^{clean}‖_{ℋ_B} ≤ L^{-G}` (mem:clean-bound): condition on shared list
and memory, drop the extra ban (cost `C_K M sup ν`), reduce by `lattice_shape` to the
determinant-exponential matrix on the box (mem:clean-kernel), Fourier-diagonalize the product
variable, Dirichlet approximation on `𝕋 ∖ 𝔐` (mem:dirichlet-minor) and the Gram bound
(mem:bilinear-gram) give `L^{0.2-A₀} + Y^{-0.1} log Y`; `A₀` independent of `K`. Correction from
refutation lane `sol-gate-b` uses the symmetric-memory projection. -/
theorem lattice_clean (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) (q_d : ℝ) (eta psi : ℝ → ℝ) :
    ∀ G : ℝ, 0 < G → ∃ A₀ : ℝ, 0 < A₀ ∧
      ∀ (K : ℕ) (F : PDFix K), F.Valid → F.Has q_d A₀ eta psi →
        ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
          ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
            ∀ w : ArchRoot, w.InRegion S → ∀ j : ℕ, j < S.N →
              MemOpNormLE_sym F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.clean j)
                (Real.rpow S.L (-G)) := by
  sorry

/-- `t2:pd.dirty-raw` — PD 04:605-714.  REPLACES the frozen `dirty_raw`.  With
`ε_K = C_K(B/M_J^K + B^K e^{-cL^{0.1}})`: every raw piece with `(St,Pr) ≠ (∅,∅)` has weighted row
sum `≤ ε_K` if `Pr ≠ ∅` (one compatible omission tuple by test (ii), mass `M_J^{-K}`,
(mem:anchor-congruence)) and `≤ C_K` otherwise, column sum `≤ ε_K` if `St ≠ ∅` and `≤ C_K`
otherwise (reversal); weighted Schur gives `‖dirty raw‖ ≤ C_K √ε_K ≤ C_K L^{1-K/200}` for large
`x` (mem:raw-dirty-norm).  Stated for `K ≥ 201`, where `ε_K ≤ 1` eventually. Correction from
refutation lane `sol-gate-b` projects each operator bound to symmetric memory. -/
theorem dirty_raw (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ), 201 ≤ K → ∀ (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ v₀ C_K c x₀ : ℝ, 1 < v₀ ∧ 0 < C_K ∧ 0 < c ∧ 2 ≤ x₀ ∧
        ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
          ∀ w : ArchRoot, w.InRegion S → ∀ j : ℕ, j < S.N →
            let B := memoryCutoff S
            let εK := C_K * ((B : ℝ) / (S.M : ℝ) ^ K +
              (B : ℝ) ^ K * Real.exp (-c * Real.rpow S.L (1 / 10 : ℝ)))
            (∀ St Pr : Finset (Fin K), ¬ (St = ∅ ∧ Pr = ∅) →
              MemRowSchurLE_sym F S B (memEdgePiece F S ρ w true St Pr j) v₀
                  (if Pr.Nonempty then εK else C_K) ∧
                MemColSchurLE_sym F S B (memEdgePiece F S ρ w true St Pr j) v₀
                  (if St.Nonempty then εK else C_K)) ∧
            MemOpNormLE_sym F S B (memEdge F S ρ w EdgeKind.dirtyRaw j)
              (C_K * Real.rpow S.L (1 - (K : ℝ) / 200)) := by
  sorry

/-- `t2:pd.dirty-comparison` — PD 04:716-770.  REPLACES the frozen `dirty_comparison`.
Comparison pieces with `(St,Pr) ≠ (∅,∅)`: a promoted index needs one prescribed line at the
target, one nonzero linear congruence in the lattice box (mem:line-count), row sum
`ζ_K = C_K L^{3A₀} B^K (p_min^{-1} + Y^{-0.1}) = O_A(L^{-A})`; the opposite side is `≤ L^C`
(mem:edge-crude); weighted Schur gives every fixed negative power of `L`. Correction from
refutation lane `sol-gate-b` projects the operator norm bound to symmetric memory. -/
theorem dirty_comparison (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ → ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S → ∀ j : ℕ, j < S.N →
          MemOpNormLE_sym F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.dirtyCmp j)
            (C_A * Real.rpow S.L (-A)) := by
  sorry

private theorem finite_weighted_schur_norm {α : Type*} [DecidableEq α]
    (μ v : α → ℝ) (k : α → α → ℂ) (f : α → ℂ) (T T' : Finset α) (a b : ℝ)
    (hμ : ∀ s, 0 ≤ μ s) (hv : ∀ s, 0 < v s) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hrow : ∀ s ∈ T', ∑ t ∈ T, ‖k s t‖ * v t ≤ a * v s)
    (hcol : ∀ t ∈ T, ∑ s ∈ T', μ s * ‖k s t‖ * v s ≤ b * μ t * v t) :
    (∑ s ∈ T', μ s * ‖∑ t ∈ T, k s t * f t‖ ^ 2) ≤
      a * b * (∑ t ∈ T, μ t * ‖f t‖ ^ 2) := by
  classical
  have hpoint (s : α) :
      ‖∑ t ∈ T, k s t * f t‖ ^ 2 ≤
        (∑ t ∈ T, ‖k s t‖ * v t) *
          ∑ t ∈ T, ‖k s t‖ * ‖f t‖ ^ 2 / v t := by
    have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (s := T)
      (r := fun t => ‖k s t‖ * ‖f t‖)
      (f := fun t => ‖k s t‖ * v t)
      (g := fun t => ‖k s t‖ * ‖f t‖ ^ 2 / v t)
      (fun t ht => mul_nonneg (norm_nonneg _) (hv t).le)
      (fun t ht => div_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) (hv t).le)
      (fun t ht => by
        have hvt := hv t
        have heq : (‖k s t‖ * ‖f t‖) ^ 2 =
            (‖k s t‖ * v t) * (‖k s t‖ * ‖f t‖ ^ 2 / v t) := by
          field_simp [hvt.ne']
        exact heq.le)
    have htri :
        ‖∑ t ∈ T, k s t * f t‖ ≤ ∑ t ∈ T, ‖k s t‖ * ‖f t‖ := by
      calc
        ‖∑ t ∈ T, k s t * f t‖ ≤ ∑ t ∈ T, ‖k s t * f t‖ := norm_sum_le _ _
        _ = ∑ t ∈ T, ‖k s t‖ * ‖f t‖ := by simp [norm_mul]
    have hsumNonneg : 0 ≤ ∑ t ∈ T, ‖k s t‖ * ‖f t‖ :=
      Finset.sum_nonneg fun t ht => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsq : ‖∑ t ∈ T, k s t * f t‖ ^ 2 ≤
        (∑ t ∈ T, ‖k s t‖ * ‖f t‖) ^ 2 := by
      have hprod := mul_nonneg (sub_nonneg.mpr htri)
        (add_nonneg (norm_nonneg (∑ t ∈ T, k s t * f t)) hsumNonneg)
      nlinarith [hprod]
    exact hsq.trans hCS
  have hinnerNonneg (s : α) :
      0 ≤ ∑ t ∈ T, ‖k s t‖ * ‖f t‖ ^ 2 / v t :=
    Finset.sum_nonneg fun t ht =>
      div_nonneg (mul_nonneg (norm_nonneg _) (sq_nonneg _)) (hv t).le
  have hrowAll (s : α) (hs : s ∈ T') :
      0 ≤ ∑ t ∈ T, ‖k s t‖ * v t :=
    Finset.sum_nonneg fun t ht => mul_nonneg (norm_nonneg _) (hv t).le
  have hswap :
      (∑ s ∈ T', μ s * v s *
        (∑ t ∈ T, ‖k s t‖ * ‖f t‖ ^ 2 / v t)) =
        ∑ t ∈ T, (‖f t‖ ^ 2 / v t) *
          (∑ s ∈ T', μ s * ‖k s t‖ * v s) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro s hs
    ring
  calc
    (∑ s ∈ T', μ s * ‖∑ t ∈ T, k s t * f t‖ ^ 2)
        ≤ ∑ s ∈ T', μ s *
          ((∑ t ∈ T, ‖k s t‖ * v t) *
            ∑ t ∈ T, ‖k s t‖ * ‖f t‖ ^ 2 / v t) := by
          apply Finset.sum_le_sum
          intro s hs
          exact mul_le_mul_of_nonneg_left (hpoint s) (hμ s)
    _ ≤ ∑ s ∈ T', μ s * ((a * v s) *
          ∑ t ∈ T, ‖k s t‖ * ‖f t‖ ^ 2 / v t) := by
          apply Finset.sum_le_sum
          intro s hs
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (hrow s hs) (hinnerNonneg s)) (hμ s)
    _ = a * (∑ s ∈ T', μ s * v s *
          (∑ t ∈ T, ‖k s t‖ * ‖f t‖ ^ 2 / v t)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          ring
    _ = a * (∑ t ∈ T, (‖f t‖ ^ 2 / v t) *
          (∑ s ∈ T', μ s * ‖k s t‖ * v s)) := by rw [hswap]
    _ ≤ a * (∑ t ∈ T, (‖f t‖ ^ 2 / v t) * (b * μ t * v t)) := by
          apply mul_le_mul_of_nonneg_left
          · apply Finset.sum_le_sum
            intro t ht
            exact mul_le_mul_of_nonneg_left (hcol t ht)
              (div_nonneg (sq_nonneg _) (hv t).le)
          · exact ha
    _ = a * b * (∑ t ∈ T, μ t * ‖f t‖ ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          have hvt := hv t
          field_simp [hvt.ne']

private theorem memOpNormLE_fintype_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (ops : ι → (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (c : ι → ℝ)
    (hμ : ∀ s, 0 ≤ memMeasure F S s) (hc : ∀ i, 0 ≤ c i)
    (hops : ∀ i, MemOpNormLE F S B (ops i) (c i)) :
    MemOpNormLE F S B (fun f s => ∑ i, ops i f s)
      (Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, c i ^ 2)) := by
  classical
  intro T T' f hsupp hT hT'
  have hpoint (s : MemPoint S.x K) :
      ‖∑ i, ops i f s‖ ^ 2 ≤
        (Fintype.card ι : ℝ) * ∑ i, ‖ops i f s‖ ^ 2 := by
    have htri : ‖∑ i, ops i f s‖ ≤ ∑ i, ‖ops i f s‖ := norm_sum_le _ _
    have hnonneg : 0 ≤ ∑ i, ‖ops i f s‖ := Finset.sum_nonneg fun i hi => norm_nonneg _
    have hcs : (∑ i, ‖ops i f s‖) ^ 2 ≤
        (Fintype.card ι : ℝ) * ∑ i, ‖ops i f s‖ ^ 2 := by
      simpa using (_root_.sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset ι)) (f := fun i => ‖ops i f s‖))
    have hprod := mul_nonneg (sub_nonneg.mpr htri)
      (add_nonneg (norm_nonneg (∑ i, ops i f s)) hnonneg)
    nlinarith [hprod, hcs]
  have hOp (i : ι) := hops i T T' f hsupp hT hT'
  have hsumOp :
      (∑ i, ∑ s ∈ T', memMeasure F S s * ‖ops i f s‖ ^ 2) ≤
        (∑ i, c i ^ 2) * memNormSqOn F S T f := by
    calc
      (∑ i, ∑ s ∈ T', memMeasure F S s * ‖ops i f s‖ ^ 2) ≤
          ∑ i, c i ^ 2 * memNormSqOn F S T f := by
            apply Finset.sum_le_sum
            intro i hi
            exact hOp i
      _ = (∑ i, c i ^ 2) * memNormSqOn F S T f := by
            rw [← Finset.sum_mul]
  unfold memNormSqOn
  calc
    (∑ s ∈ T', memMeasure F S s * ‖∑ i, ops i f s‖ ^ 2) ≤
        ∑ s ∈ T', memMeasure F S s *
          ((Fintype.card ι : ℝ) * ∑ i, ‖ops i f s‖ ^ 2) := by
            apply Finset.sum_le_sum
            intro s hs
            exact mul_le_mul_of_nonneg_left (hpoint s) (hμ s)
    _ = (Fintype.card ι : ℝ) *
          (∑ i, ∑ s ∈ T', memMeasure F S s * ‖ops i f s‖ ^ 2) := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro s hs
            ring
    _ ≤ (Fintype.card ι : ℝ) *
          ((∑ i, c i ^ 2) * (∑ s ∈ T, memMeasure F S s * ‖f s‖ ^ 2)) := by
            exact mul_le_mul_of_nonneg_left hsumOp (by positivity)
    _ = (Real.sqrt ((Fintype.card ι : ℝ) * ∑ i, c i ^ 2)) ^ 2 *
          (∑ s ∈ T, memMeasure F S s * ‖f s‖ ^ 2) := by
            rw [Real.sq_sqrt (by positivity : 0 ≤ (Fintype.card ι : ℝ) * ∑ i, c i ^ 2)]
            ring

private theorem memOpNormLE_add_sub {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (A D E : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (a d e : ℝ)
    (hμ : ∀ s, 0 ≤ memMeasure F S s)
    (hA : MemOpNormLE F S B A a) (hD : MemOpNormLE F S B D d)
    (hE : MemOpNormLE F S B E e) :
    MemOpNormLE F S B (fun f s => A f s + D f s - E f s)
      (Real.sqrt (3 * (a ^ 2 + d ^ 2 + e ^ 2))) := by
  classical
  intro T T' f hsupp hT hT'
  have hA' := hA T T' f hsupp hT hT'
  have hD' := hD T T' f hsupp hT hT'
  have hE' := hE T T' f hsupp hT hT'
  have hpoint (s : MemPoint S.x K) :
      ‖A f s + D f s - E f s‖ ^ 2 ≤
        3 * (‖A f s‖ ^ 2 + ‖D f s‖ ^ 2 + ‖E f s‖ ^ 2) := by
    have htriangle : ‖A f s + D f s - E f s‖ ≤ ‖A f s‖ + ‖D f s‖ + ‖E f s‖ := by
      calc
        ‖A f s + D f s - E f s‖ ≤ ‖A f s + D f s‖ + ‖E f s‖ := norm_sub_le _ _
        _ ≤ ‖A f s‖ + ‖D f s‖ + ‖E f s‖ := by gcongr; exact norm_add_le _ _
    have ha : 0 ≤ ‖A f s‖ := norm_nonneg _
    have hd : 0 ≤ ‖D f s‖ := norm_nonneg _
    have he : 0 ≤ ‖E f s‖ := norm_nonneg _
    have hdiff : 0 ≤ (‖A f s‖ + ‖D f s‖ + ‖E f s‖) - ‖A f s + D f s - E f s‖ := by
      linarith [htriangle]
    have hsum : 0 ≤ ‖A f s‖ + ‖D f s‖ + ‖E f s‖ + ‖A f s + D f s - E f s‖ := by
      positivity
    have hsq : ‖A f s + D f s - E f s‖ ^ 2 ≤
        (‖A f s‖ + ‖D f s‖ + ‖E f s‖) ^ 2 := by
      nlinarith [mul_nonneg hdiff hsum]
    nlinarith [hsq, sq_nonneg (‖A f s‖ - ‖D f s‖),
      sq_nonneg (‖A f s‖ - ‖E f s‖), sq_nonneg (‖D f s‖ - ‖E f s‖)]
  have hsum :
      (∑ s ∈ T', memMeasure F S s * ‖A f s‖ ^ 2) +
          (∑ s ∈ T', memMeasure F S s * ‖D f s‖ ^ 2) +
          (∑ s ∈ T', memMeasure F S s * ‖E f s‖ ^ 2) ≤
        (a ^ 2 + d ^ 2 + e ^ 2) * memNormSqOn F S T f := by
    unfold memNormSqOn at hA' hD' hE' ⊢
    linarith
  unfold memNormSqOn
  calc
    (∑ s ∈ T', memMeasure F S s * ‖A f s + D f s - E f s‖ ^ 2) ≤
        ∑ s ∈ T', memMeasure F S s *
          (3 * (‖A f s‖ ^ 2 + ‖D f s‖ ^ 2 + ‖E f s‖ ^ 2)) := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left (hpoint s) (hμ s)
    _ = 3 * ((∑ s ∈ T', memMeasure F S s * ‖A f s‖ ^ 2) +
          (∑ s ∈ T', memMeasure F S s * ‖D f s‖ ^ 2) +
          (∑ s ∈ T', memMeasure F S s * ‖E f s‖ ^ 2)) := by
      rw [show (fun s => memMeasure F S s *
            (3 * (‖A f s‖ ^ 2 + ‖D f s‖ ^ 2 + ‖E f s‖ ^ 2))) =
          (fun s => 3 * (memMeasure F S s * ‖A f s‖ ^ 2) +
            (3 * (memMeasure F S s * ‖D f s‖ ^ 2) +
              3 * (memMeasure F S s * ‖E f s‖ ^ 2))) by
        funext s
        ring]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring
    _ ≤ 3 * ((a ^ 2 + d ^ 2 + e ^ 2) * memNormSqOn F S T f) := by
      nlinarith [hsum]
    _ = (Real.sqrt (3 * (a ^ 2 + d ^ 2 + e ^ 2))) ^ 2 * memNormSqOn F S T f := by
      rw [Real.sq_sqrt (by positivity : 0 ≤ 3 * (a ^ 2 + d ^ 2 + e ^ 2))]
      ring

private theorem sum_sum_split_empty {γ : Type*} [Fintype γ] [DecidableEq γ]
    (f : Finset γ → Finset γ → ℂ) :
    (∑ x : Finset γ, ∑ y : Finset γ, f x y) = f ∅ ∅ +
      ∑ x : Finset γ, ∑ y : Finset γ, if x = ∅ ∧ y = ∅ then 0 else f x y := by
  classical
  let U : Finset (Finset γ) := Finset.univ
  have hempty : (∅ : Finset γ) ∈ U := by simp [U]
  have hraw0 : (∑ y : Finset γ, f ∅ y) = f ∅ ∅ +
      ∑ y ∈ U.erase ∅, f ∅ y := by
    rw [← Finset.sum_erase_add U (fun y => f ∅ y) hempty, add_comm]
  have hdirty0 : (∑ y : Finset γ, if (∅ : Finset γ) = ∅ ∧ y = ∅ then 0 else f ∅ y) =
      ∑ y ∈ U.erase ∅, f ∅ y := by
    rw [← Finset.sum_erase_add U
      (fun y => if (∅ : Finset γ) = ∅ ∧ y = ∅ then 0 else f ∅ y) hempty]
    have hErase : (∑ y ∈ U.erase ∅,
        if (∅ : Finset γ) = ∅ ∧ y = ∅ then 0 else f ∅ y) =
        ∑ y ∈ U.erase ∅, f ∅ y := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyne : y ≠ ∅ := (Finset.mem_erase.mp hy).1
      simp [hyne]
    rw [hErase]
    simp only [true_and, ite_true, add_zero]
  have hoff (x : Finset γ) (hx : x ∈ U.erase ∅) :
      (∑ y : Finset γ, if x = ∅ ∧ y = ∅ then 0 else f x y) =
        ∑ y : Finset γ, f x y := by
    have hxne : x ≠ ∅ := (Finset.mem_erase.mp hx).1
    simp [hxne]
  have hraw : (∑ x : Finset γ, ∑ y : Finset γ, f x y) =
      f ∅ ∅ + (∑ x ∈ U.erase ∅, ∑ y : Finset γ, f x y) +
        ∑ y ∈ U.erase ∅, f ∅ y := by
    rw [← Finset.sum_erase_add U (fun x => ∑ y : Finset γ, f x y) hempty, hraw0]
    ring
  have hdirty : (∑ x : Finset γ,
      ∑ y : Finset γ, if x = ∅ ∧ y = ∅ then 0 else f x y) =
      (∑ x ∈ U.erase ∅, ∑ y : Finset γ, f x y) +
        ∑ y ∈ U.erase ∅, f ∅ y := by
    rw [← Finset.sum_erase_add U
      (fun x => ∑ y : Finset γ, if x = ∅ ∧ y = ∅ then 0 else f x y) hempty]
    rw [Finset.sum_congr rfl (fun x hx => hoff x hx), hdirty0]
  rw [hraw, hdirty]
  ring

private theorem memEdge_full_eq_clean_add_dirty {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (j : ℕ) (f : MemPoint S.x K → ℂ) :
    memEdge F S ρ w EdgeKind.full j f =
      memEdge F S ρ w EdgeKind.clean j f + memEdge F S ρ w EdgeKind.dirtyRaw j f -
        memEdge F S ρ w EdgeKind.dirtyCmp j f := by
  classical
  funext s
  simp only [memEdge, plainOp, logEdge, logSym]
  dsimp [plainOp, logEdge, logSym]
  simp_rw [Finset.sum_sub_distrib]
  have hraw (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :=
    sum_sum_split_empty (fun St Pr =>
      logEdgePiece F S ρ w j true St Pr (logSym F S fun σL => f σL.1)
        ((s.1, permuteLists σ s.2.1, s.2.2), []))
  have hcmp (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :=
    sum_sum_split_empty (fun St Pr =>
      logEdgePiece F S ρ w j false St Pr (logSym F S fun σL => f σL.1)
        ((s.1, permuteLists σ s.2.1, s.2.2), []))
  simp_rw [hraw, hcmp, Finset.sum_add_distrib]
  ring_nf

private theorem memEdge_dirtyRaw_eq_piece_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (j : ℕ) :
    memEdge F S ρ w EdgeKind.dirtyRaw j =
      (fun f s => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (if St = ∅ ∧ Pr = ∅ then 0 else
          memEdgePiece F S ρ w true St Pr j f s)) := by
  funext f s
  simp only [memEdge, plainOp, logEdge, memEdgePiece]
  dsimp [logSym]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro St hSt
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Pr hPr
  by_cases hempty : St = ∅ ∧ Pr = ∅ <;> simp [hempty]

private theorem memEdge_dirtyCmp_eq_piece_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (j : ℕ) :
    memEdge F S ρ w EdgeKind.dirtyCmp j =
      (fun f s => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (if St = ∅ ∧ Pr = ∅ then 0 else
          memEdgePiece F S ρ w false St Pr j f s)) := by
  funext f s
  simp only [memEdge, plainOp, logEdge, memEdgePiece]
  dsimp [logSym]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro St hSt
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro Pr hPr
  by_cases hempty : St = ∅ ∧ Pr = ∅ <;> simp [hempty]

private theorem memMeasure_eq_zero_of_nonprimitive {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (h : Int.gcd s.1.1 s.1.2 ≠ 1) :
    memMeasure F S s = 0 := by
  have hv : ¬ MemValid F S s := by
    intro hs
    exact h hs.1
  simp [memMeasure, hv]

private theorem memOpNormLE_zero_from_null_source {K : ℕ} (F : PDFix K) (S : PDScale)
    (B : ℕ) (op : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (c : ℝ)
    (hOp : MemOpNormLE F S B op c) (s t : MemPoint S.x K)
    (hs : memSize s ≤ B) (ht : memSize t ≤ B)
    (hμs : memMeasure F S s = 0) (hμt : 0 < memMeasure F S t) :
    op (fun u => if u = s then 1 else 0) t = 0 := by
  have hsupport : ∀ u, u ∉ ({s} : Finset (MemPoint S.x K)) →
      (if u = s then (1 : ℂ) else 0) = 0 := by
    intro u hu
    simp only [Finset.mem_singleton] at hu
    simp [hu]
  have hT : ∀ u ∈ ({s} : Finset (MemPoint S.x K)), memSize u ≤ B := by
    intro u hu
    simpa [Finset.mem_singleton.mp hu] using hs
  have hT' : ∀ u ∈ ({t} : Finset (MemPoint S.x K)), memSize u ≤ B := by
    intro u hu
    simpa [Finset.mem_singleton.mp hu] using ht
  have h := hOp {s} {t} (fun u => if u = s then 1 else 0) hsupport hT hT'
  simp [memNormSqOn, hμs] at h
  have hnonneg : 0 ≤ memMeasure F S t *
      ‖op (fun u => if u = s then 1 else 0) t‖ ^ 2 :=
    mul_nonneg hμt.le (sq_nonneg _)
  have hzero : memMeasure F S t *
      ‖op (fun u => if u = s then 1 else 0) t‖ ^ 2 = 0 := le_antisymm h hnonneg
  have hnormsq : ‖op (fun u => if u = s then 1 else 0) t‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp hzero with hμt0 | hnormsq
    · exact (hμt.ne' hμt0).elim
    · exact hnormsq
  have hnorm : ‖op (fun u => if u = s then 1 else 0) t‖ = 0 := by
    nlinarith [sq_nonneg (‖op (fun u => if u = s then 1 else 0) t‖)]
  exact norm_eq_zero.mp hnorm

private theorem memMeasure_nonneg_for_large {K : ℕ} (F : PDFix K) (hF : F.Valid) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, x₀ ≤ S.x →
      ∀ s : MemPoint S.x K, 0 ≤ memMeasure F S s := by
  classical
  have hBands : ValidBands K F.a := hF.1
  have hbandExist : ∀ i : Fin K,
      ∃ xᵢ : ℝ, 2 ≤ xᵢ ∧ ∀ x : ℝ, xᵢ ≤ x → 0 < bandMass x (F.a i) := by
    intro i
    have ha₀ : 0 < F.a i := by
      have := hBands.2.1 i
      linarith
    have ha₁ : F.a i < 1 := by
      have := hBands.2.1 i
      linarith
    have hε : 0 < Real.log 2 / 2 := by positivity
    obtain ⟨xᵢ, hxᵢ, hmass⟩ := band_mass (F.a i) ha₀ ha₁ (Real.log 2 / 2) hε
    exact ⟨xᵢ, hxᵢ, fun x hx => (hmass x hx).2⟩
  choose xBand hxBand using hbandExist
  have hK : 0 < K := hBands.1
  let i₀ : Fin K := ⟨0, hK⟩
  have hU : (Finset.univ : Finset (Fin K)).Nonempty := ⟨i₀, Finset.mem_univ _⟩
  let xBandMax : ℝ := Finset.univ.sup' hU xBand
  have hxBandMax (i : Fin K) : xBand i ≤ xBandMax :=
    Finset.le_sup' (f := xBand) (Finset.mem_univ i)
  have hxBandMax₂ : 2 ≤ xBandMax := by
    exact le_trans (hxBand i₀).1 (hxBandMax i₀)
  have hratioEv : ∀ᶠ t : ℝ in Filter.atTop, 2 < Real.exp t / t ^ 5 :=
    (Real.tendsto_exp_div_pow_atTop 5).eventually_gt_atTop 2
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.1 hratioEv
  let T : ℝ := max t₀ 3
  have hT3 : 3 ≤ T := le_max_right _ _
  have hTt₀ : t₀ ≤ T := le_max_left _ _
  let x₀ : ℝ := max xBandMax (Real.exp (T ^ 10))
  refine ⟨x₀, le_trans hxBandMax₂ (le_max_left _ _), ?_⟩
  intro S hx₀ s
  have hxBandS : xBandMax ≤ S.x := le_trans (le_max_left _ _) hx₀
  have hxExp : Real.exp (T ^ 10) ≤ S.x := le_trans (le_max_right _ _) hx₀
  let L : ℝ := Real.log S.x
  have hlog : T ^ 10 ≤ L := by
    have h := Real.log_le_log (Real.exp_pos (T ^ 10)) hxExp
    simpa [L] using h
  have hLpos : 0 < L := by
    have : 0 < T ^ 10 := by positivity
    dsimp [L]
    exact lt_of_lt_of_le this hlog
  have hLone : 1 ≤ L := by
    have hT : (1 : ℝ) ≤ T := by linarith
    have hTpow : (1 : ℝ) ≤ T ^ 10 := one_le_pow₀ hT
    exact hTpow.trans hlog
  let t : ℝ := Real.rpow L (1 / 10 : ℝ)
  have hTle : T ≤ t := by
    calc
      T = Real.rpow (T ^ 10) (1 / 10 : ℝ) := by
        simpa [div_eq_mul_inv] using
          (Real.pow_rpow_inv_natCast (by positivity : 0 ≤ T) (by norm_num : 10 ≠ 0)).symm
      _ ≤ Real.rpow L (1 / 10 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hlog (by norm_num)
  have ht₀t : t₀ ≤ t := hTt₀.trans hTle
  have hratio : 2 < Real.exp t / t ^ 5 := ht₀ t ht₀t
  have htpos : 0 < t := by dsimp [t]; positivity
  have hpowPos : 0 < t ^ 5 := pow_pos htpos _
  have hExpT : 2 * t ^ 5 < Real.exp t := (lt_div_iff₀ hpowPos).mp hratio
  have ht₃ : 3 ≤ t := hT3.trans hTle
  have hpowLower : (3 : ℝ) ^ 5 ≤ t ^ 5 := by gcongr
  have ht5 : t ^ 5 = Real.rpow L (1 / 2 : ℝ) := by
    dsimp [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hLpos)]
    norm_num
  have hpath : (pathLength S.x : ℝ) < Real.rpow L (1 / 2 : ℝ) + 2 := by
    have hceil : (momentR S.x : ℝ) < Real.rpow L (1 / 2 : ℝ) / 2 + 1 := by
      dsimp [momentR]
      exact Nat.ceil_lt_add_one (by positivity)
    have hceil2 := mul_lt_mul_of_pos_left hceil (by norm_num : (0 : ℝ) < 2)
    dsimp [pathLength]
    push_cast
    calc
      2 * (momentR S.x : ℝ) < 2 * (Real.rpow L (1 / 2 : ℝ) / 2 + 1) := hceil2
      _ = Real.rpow L (1 / 2 : ℝ) + 2 := by ring
  have hpathExp : (pathLength S.x : ℝ) < Real.exp t := by
    calc
      (pathLength S.x : ℝ) < Real.rpow L (1 / 2 : ℝ) + 2 := hpath
      _ = t ^ 5 + 2 := by rw [ht5]
      _ ≤ 2 * t ^ 5 := by nlinarith [hpowLower]
      _ < Real.exp t := hExpT
  have hprimeLarge : ∀ i : Fin K, ∀ p : ℕ, p ∈ primeBand S.x (F.a i) →
      (pathLength S.x : ℝ) < (p : ℝ) := by
    intro i p hp
    have ha : (1 / 10 : ℝ) ≤ F.a i := (hBands.2.1 i).1.le
    have hLp : Real.rpow L (1 / 10 : ℝ) ≤ Real.rpow L (F.a i) :=
      Real.rpow_le_rpow_of_exponent_le hLone ha
    have hExpMono : Real.exp t ≤ Real.exp (Real.rpow L (F.a i)) :=
      Real.exp_le_exp.mpr hLp
    have hpLower : Real.exp (Real.rpow L (F.a i)) ≤ (p : ℝ) :=
      (Finset.mem_filter.mp hp).2.2.1
    exact lt_of_lt_of_le hpathExp (hExpMono.trans hpLower)
  have hmass (i : Fin K) : 0 < bandMass S.x (F.a i) :=
    (hxBand i).2 S.x (le_trans (hxBandMax i) hxBandS)
  have heta (j : ℕ) : memoryEta S.x F.q_d j ≤ 1 := by
    have hqd : 0 < F.q_d := hF.2.1
    have hq : 0 ≤ memoryQ S.x F.q_d j := by
      unfold memoryQ
      split_ifs <;> positivity
    unfold memoryEta
    linarith
  have hnu (i : Fin K) (p : ℕ) (hp : p ∈ primeBand S.x (F.a i)) :
      0 < memoryNu S.x K F.a F.q_d i p := by
    have hpPath : (pathLength S.x : ℝ) < (p : ℝ) := hprimeLarge i p hp
    have hpden : 0 < (p : ℝ) + 1 := by positivity
    have hcount : ((pathLength S.x + 1 : ℕ) : ℝ) < (p : ℝ) + 1 := by
      have h := add_lt_add_right hpPath 1
      simpa [Nat.cast_add] using h
    have hquot : ((pathLength S.x + 1 : ℕ) : ℝ) / ((p : ℝ) + 1) < 1 :=
      (div_lt_one hpden).2 hcount
    have hsum : (∑ j ∈ Finset.range (pathLength S.x + 1),
        memoryEta S.x F.q_d j / ((p : ℝ) + 1)) < 1 := by
      calc
        _ ≤ ∑ j ∈ Finset.range (pathLength S.x + 1), 1 / ((p : ℝ) + 1) := by
          apply Finset.sum_le_sum
          intro j hj
          exact div_le_div_of_nonneg_right (heta j) hpden.le
        _ = ((pathLength S.x + 1 : ℕ) : ℝ) / ((p : ℝ) + 1) := by
          simp [Finset.sum_const, Finset.card_range]
          ring
        _ < 1 := hquot
    have hbprime : 0 < memoryBPrime S.x F.q_d p := by
      unfold memoryBPrime
      linarith
    have hmassPos : 0 < bandMass S.x (F.a i) := hmass i
    unfold memoryNu
    positivity
  by_cases hs : MemValid F S s
  · unfold memMeasure
    rw [if_pos hs]
    apply mul_nonneg
    · apply Finset.prod_nonneg
      intro i hi
      apply Finset.prod_nonneg
      intro j hj
      exact (hnu i (s.2.1 i j) (hs.2.1 i j)).le
    · apply Finset.prod_nonneg
      intro i hi
      apply div_nonneg
      · apply List.prod_nonneg
        intro e he
        rcases List.mem_map.mp he with ⟨e', he', rfl⟩
        exact (hnu i e'.1 (hs.2.2 i e' he').1).le
      · positivity
  · simp [memMeasure, hs]

private theorem memNormSqOn_nonneg {K : ℕ} (F : PDFix K) (S : PDScale)
    (T : Finset (MemPoint S.x K)) (f : MemPoint S.x K → ℂ)
    (hμ : ∀ s, 0 ≤ memMeasure F S s) :
    0 ≤ memNormSqOn F S T f := by
  classical
  unfold memNormSqOn
  apply Finset.sum_nonneg
  intro s hs
  exact mul_nonneg (hμ s) (sq_nonneg _)

private theorem memOpNormLE_mono {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (op : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (c d : ℝ)
    (hμ : ∀ s, 0 ≤ memMeasure F S s) (h : MemOpNormLE F S B op c)
    (hc : 0 ≤ c) (hcd : c ≤ d) : MemOpNormLE F S B op d := by
  intro T T' f hsupp hT hT'
  have hinput : 0 ≤ memNormSqOn F S T f := memNormSqOn_nonneg F S T f hμ
  have hsq : c ^ 2 ≤ d ^ 2 := by nlinarith
  have hopen := h T T' f hsupp hT hT'
  nlinarith

private theorem memOpNormLE_sym_mono {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (op : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (c d : ℝ)
    (hμ : ∀ s, 0 ≤ memMeasure F S s) (h : MemOpNormLE_sym F S B op c)
    (hc : 0 ≤ c) (hcd : c ≤ d) : MemOpNormLE_sym F S B op d := by
  change MemOpNormLE F S B (fun f => op (memorySym f)) c at h
  change MemOpNormLE F S B (fun f => op (memorySym f)) d
  exact memOpNormLE_mono F S B (fun f => op (memorySym f)) c d hμ h hc hcd

private theorem memOpNormLE_sym_add_sub {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (A D E : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (a d e : ℝ)
    (hμ : ∀ s, 0 ≤ memMeasure F S s)
    (hA : MemOpNormLE_sym F S B A a) (hD : MemOpNormLE_sym F S B D d)
    (hE : MemOpNormLE_sym F S B E e) :
    MemOpNormLE_sym F S B (fun f s => A f s + D f s - E f s)
      (Real.sqrt (3 * (a ^ 2 + d ^ 2 + e ^ 2))) := by
  change MemOpNormLE F S B (fun f => A (memorySym f)) a at hA
  change MemOpNormLE F S B (fun f => D (memorySym f)) d at hD
  change MemOpNormLE F S B (fun f => E (memorySym f)) e at hE
  change MemOpNormLE F S B
    (fun f s => A (memorySym f) s + D (memorySym f) s - E (memorySym f) s) _
  exact memOpNormLE_add_sub F S B
    (fun f => A (memorySym f)) (fun f => D (memorySym f)) (fun f => E (memorySym f))
    a d e hμ hA hD hE

/-- `t2:pd.signed-edge` (new assembly node) — PD 04:772-782 (mem:signed-edge).  Choose `A₀`
from `lattice_clean` for `G+1`, then `K₀` with `K₀/200 > G+2`: `‖ℰ_j‖_{ℋ_B} ≤ L^{-G}`
(`ℰ_j = clean + dirtyRaw - dirtyCmp` by definition). Correction from refutation lane
`sol-gate-b` composes the symmetric-memory projected bounds. -/
theorem signed_edge (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) (q_d : ℝ) (eta psi : ℝ → ℝ) :
    ∀ G : ℝ, 0 < G → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ,
      ∀ (K : ℕ), K₀ ≤ K → ∀ (F : PDFix K), F.Valid → F.Has q_d A₀ eta psi →
        ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
          ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
            ∀ w : ArchRoot, w.InRegion S → ∀ j : ℕ, j < S.N →
              MemOpNormLE_sym F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.full j)
                (Real.rpow S.L (-G)) := by
  intro G hG
  have hG3 : 0 < G + 3 := by linarith
  obtain ⟨A₀, hA₀, hCleanAll⟩ := lattice_clean δ c₁ c₂ hδ hc₁ q_d eta psi (G + 3) hG3
  let K₀ : ℕ := max 201 ⌈200 * (G + 4)⌉₊
  have hK₀ : 201 ≤ K₀ := le_max_left _ _
  have hKceil : (⌈200 * (G + 4)⌉₊ : ℝ) ≤ K₀ := by
    exact_mod_cast (le_max_right 201 ⌈200 * (G + 4)⌉₊)
  have hceil : 200 * (G + 4) ≤ (⌈200 * (G + 4)⌉₊ : ℝ) := Nat.le_ceil _
  refine ⟨A₀, hA₀, K₀, ?_⟩
  intro K hK F hF hHas ρ hρ
  have hKcast : (K₀ : ℝ) ≤ K := by exact_mod_cast hK
  have hKlower : 200 * (G + 4) ≤ (K : ℝ) := le_trans hceil (le_trans hKceil hKcast)
  have hExponent : 1 - (K : ℝ) / 200 ≤ -(G + 3) := by
    have hKlower' : (G + 4) * 200 ≤ (K : ℝ) := by simpa [mul_comm] using hKlower
    have hdiv : G + 4 ≤ (K : ℝ) / 200 :=
      (le_div_iff₀ (by norm_num : (0 : ℝ) < 200)).2 hKlower'
    linarith
  obtain ⟨v₀, C_K, c, xRaw, hv₀, hC_K, hc, hxRaw, hRawAll⟩ :=
    dirty_raw δ c₁ c₂ hδ hc₁ K (le_trans hK₀ hK) F hF ρ hρ
  obtain ⟨Ccmp, xCmp, hCcmp, hxCmp, hCmpAll⟩ :=
    dirty_comparison δ c₁ c₂ hδ hc₁ K F hF ρ hρ (G + 3) hG3
  obtain ⟨xClean, hxClean, hClean⟩ := hCleanAll K F hF hHas ρ hρ
  obtain ⟨xMeasure, hxMeasure, hMeasure⟩ := memMeasure_nonneg_for_large F hF
  let xLarge : ℝ := 3 * (1 + C_K + Ccmp)
  let x₀ : ℝ := max xClean (max xRaw (max xCmp (max xMeasure (Real.exp xLarge))))
  have hx₀₂ : 2 ≤ x₀ := le_trans hxClean (le_max_left _ _)
  refine ⟨x₀, hx₀₂, ?_⟩
  intro S hS hx₀ w hw j hj
  have hxClean₀ : xClean ≤ x₀ := le_max_left _ _
  have hxRaw₀ : xRaw ≤ x₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hxCmp₀ : xCmp ≤ x₀ :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hxMeasure₀ : xMeasure ≤ x₀ :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hxExp₀ : Real.exp xLarge ≤ x₀ :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hμ : ∀ s, 0 ≤ memMeasure F S s := hMeasure S (le_trans hxMeasure₀ hx₀)
  have hLlarge : xLarge ≤ S.L := by
    have hexp : Real.exp xLarge ≤ S.x := le_trans hxExp₀ hx₀
    have hlog := Real.log_le_log (Real.exp_pos xLarge) hexp
    simpa [PDScale.L] using hlog
  have hxLarge3 : 3 ≤ xLarge := by
    dsimp [xLarge]
    nlinarith [hC_K, hCcmp]
  have hLone : 1 ≤ S.L := le_trans (by norm_num : (1 : ℝ) ≤ 3) (le_trans hxLarge3 hLlarge)
  have hLpos : 0 < S.L := lt_of_lt_of_le zero_lt_one hLone
  have hLcube : S.L ≤ S.L ^ 3 := by
    calc
      S.L = S.L * 1 := by ring
      _ ≤ S.L * S.L ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hLone) hLpos.le
      _ = S.L ^ 3 := by ring
  have hThreeCK : 3 * C_K ≤ S.L := by
    have : 3 * C_K ≤ xLarge := by dsimp [xLarge]; nlinarith [hCcmp]
    exact this.trans hLlarge
  have hThreeCmp : 3 * Ccmp ≤ S.L := by
    have : 3 * Ccmp ≤ xLarge := by dsimp [xLarge]; nlinarith [hC_K]
    exact this.trans hLlarge
  have hThree : 3 ≤ S.L := by
    have : (3 : ℝ) ≤ xLarge := hxLarge3
    exact this.trans hLlarge
  have hCoefOne : 1 ≤ S.L ^ 3 / 3 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith [hLcube, hThree]
  have hCoefRaw : C_K ≤ S.L ^ 3 / 3 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith [hLcube, hThreeCK]
  have hCoefCmp : Ccmp ≤ S.L ^ 3 / 3 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
    nlinarith [hLcube, hThreeCmp]
  have hfac : Real.rpow S.L (-G) = Real.rpow S.L (-(G + 3)) * S.L ^ 3 := by
    calc
      Real.rpow S.L (-G) = Real.rpow S.L (-(G + 3) + 3) := by congr 1 <;> ring
      _ = Real.rpow S.L (-(G + 3)) * Real.rpow S.L 3 := Real.rpow_add hLpos _ _
      _ = Real.rpow S.L (-(G + 3)) * Real.rpow S.L ((3 : ℕ) : ℝ) := by norm_num
      _ = Real.rpow S.L (-(G + 3)) * S.L ^ 3 := by
        exact congrArg (fun q : ℝ => Real.rpow S.L (-(G + 3)) * q)
          (Real.rpow_natCast S.L (3 : ℕ))
  have hthird (C : ℝ) (hC : 0 ≤ C) (hCoef : C ≤ S.L ^ 3 / 3) :
      C * Real.rpow S.L (-(G + 3)) ≤ Real.rpow S.L (-G) / 3 := by
    have hr : 0 < Real.rpow S.L (-(G + 3)) := Real.rpow_pos_of_pos hLpos _
    rw [hfac]
    calc
      C * Real.rpow S.L (-(G + 3)) ≤ (S.L ^ 3 / 3) * Real.rpow S.L (-(G + 3)) :=
        mul_le_mul_of_nonneg_right hCoef hr.le
      _ = (Real.rpow S.L (-(G + 3)) * S.L ^ 3) / 3 := by ring
  have hOneThird : Real.rpow S.L (-(G + 3)) ≤ Real.rpow S.L (-G) / 3 := by
    simpa using hthird 1 (by norm_num) hCoefOne
  have hRawData := hRawAll S hS (le_trans hxRaw₀ hx₀) w hw j hj
  have hRawOld : MemOpNormLE_sym F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.dirtyRaw j)
      (C_K * Real.rpow S.L (1 - (K : ℝ) / 200)) := hRawData.2
  have hRawCoeffPos : 0 ≤ C_K * Real.rpow S.L (1 - (K : ℝ) / 200) :=
    mul_nonneg hC_K.le (Real.rpow_pos_of_pos hLpos _).le
  have hRpow : Real.rpow S.L (1 - (K : ℝ) / 200) ≤ Real.rpow S.L (-(G + 3)) :=
    Real.rpow_le_rpow_of_exponent_le hLone hExponent
  have hRawCoeff : C_K * Real.rpow S.L (1 - (K : ℝ) / 200) ≤
      C_K * Real.rpow S.L (-(G + 3)) := mul_le_mul_of_nonneg_left hRpow hC_K.le
  have hRawCoeffThird : C_K * Real.rpow S.L (-(G + 3)) ≤ Real.rpow S.L (-G) / 3 :=
    hthird C_K hC_K.le hCoefRaw
  have hCleanOp := hClean S hS (le_trans hxClean₀ hx₀) w hw j hj
  have hCleanOp' := memOpNormLE_sym_mono F S (memoryCutoff S)
    (memEdge F S ρ w EdgeKind.clean j) (Real.rpow S.L (-(G + 3)))
    (Real.rpow S.L (-G) / 3) hμ hCleanOp
    (Real.rpow_pos_of_pos hLpos _).le hOneThird
  have hRawOp' := memOpNormLE_sym_mono F S (memoryCutoff S)
    (memEdge F S ρ w EdgeKind.dirtyRaw j)
    (C_K * Real.rpow S.L (1 - (K : ℝ) / 200)) (C_K * Real.rpow S.L (-(G + 3)))
    hμ hRawOld hRawCoeffPos hRawCoeff
  have hRawOp'' := memOpNormLE_sym_mono F S (memoryCutoff S)
    (memEdge F S ρ w EdgeKind.dirtyRaw j) (C_K * Real.rpow S.L (-(G + 3)))
    (Real.rpow S.L (-G) / 3) hμ hRawOp'
    (mul_nonneg hC_K.le (Real.rpow_pos_of_pos hLpos _).le) hRawCoeffThird
  have hCmpData := hCmpAll S hS (le_trans hxCmp₀ hx₀) w hw j hj
  have hCmpOp := memOpNormLE_sym_mono F S (memoryCutoff S)
    (memEdge F S ρ w EdgeKind.dirtyCmp j)
    (Ccmp * Real.rpow S.L (-(G + 3))) (Real.rpow S.L (-G) / 3) hμ hCmpData
    (mul_nonneg hCcmp.le (Real.rpow_pos_of_pos hLpos _).le)
    (hthird Ccmp hCcmp.le hCoefCmp)
  have hArg : 3 * ((Real.rpow S.L (-G) / 3) ^ 2 +
      (Real.rpow S.L (-G) / 3) ^ 2 + (Real.rpow S.L (-G) / 3) ^ 2) =
      (Real.rpow S.L (-G)) ^ 2 := by ring
  have hRnonneg : 0 ≤ Real.rpow S.L (-G) := (Real.rpow_pos_of_pos hLpos _).le
  have hConst : Real.sqrt (3 * ((Real.rpow S.L (-G) / 3) ^ 2 +
      (Real.rpow S.L (-G) / 3) ^ 2 + (Real.rpow S.L (-G) / 3) ^ 2)) =
      Real.rpow S.L (-G) := by
    rw [hArg, Real.sqrt_sq_eq_abs, abs_of_nonneg hRnonneg]
  have hTriangle := memOpNormLE_sym_add_sub F S (memoryCutoff S)
    (memEdge F S ρ w EdgeKind.clean j) (memEdge F S ρ w EdgeKind.dirtyRaw j)
    (memEdge F S ρ w EdgeKind.dirtyCmp j) (Real.rpow S.L (-G) / 3)
    (Real.rpow S.L (-G) / 3) (Real.rpow S.L (-G) / 3) hμ hCleanOp' hRawOp'' hCmpOp
  rw [hConst] at hTriangle
  have hEdge : memEdge F S ρ w EdgeKind.full j =
      (fun f s => memEdge F S ρ w EdgeKind.clean j f s +
        memEdge F S ρ w EdgeKind.dirtyRaw j f s - memEdge F S ρ w EdgeKind.dirtyCmp j f s) := by
    funext f s
    exact congrFun (memEdge_full_eq_clean_add_dirty F S ρ w j f) s
  rw [hEdge]
  exact hTriangle

/-- `t2:pd.birth-partition` (new node, general) — PD 04:807-823 (mem:partition-identity).  For a
log whose addresses are distinct and lie in `A`, the distinctness weight is the signed sum of the
constraint weights: `Σ_π sgn π` over value-preserving permutations of the performed addresses,
grouped by nontrivial cycles (`(|C|-1)!` cyclic orders of sign `(-1)^{|C|-1}` on each block). -/
theorem birth_partition {K : ℕ} (A : Finset (BirthAddress K)) (log : BirthLog K)
    (hnodup : (log.map Prod.fst).Nodup) (hA : ∀ e ∈ log, e.1 ∈ A) :
    distinctWeight log =
      ∑ 𝒞 ∈ constraintSystems A, (constraintCoeff 𝒞 : ℂ) * constraintWeight 𝒞 log := by
  exact birth_partition_from_labels A log hnodup hA

/-- `t2:pd.history-rank-high` (new node) — PD 04:825-904.  High-rank constraint systems are
negligible in absolute value: with `r₀ = ⌈C' N log L / L^{0.1}⌉` (`C'` large after the crude
exponent), `Σ_{r(𝒞) ≥ r₀} |coef 𝒞| · |H_𝒞| ≤ L^{-(E₀+3)N}`, where `H_𝒞` is the truncated history
with final weight `constraintWeight 𝒞`.  Proof: coefficient mass `Q_birth^{2r}` (mem:rank-coefficients);
a fixed system costs `L^{C(N+1)} (C_K e^{-L^{0.1}})^r` by chronological conditioning on pivots, an
atom `Δ ≤ C_K e^{-L^{0.1}}` per nonpivot birth (mem:edge-atoms), (mem:ghost-atoms); geometric
series (mem:high-rank). -/
theorem history_rank_high (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ → ∀ E₀ : ℝ, 0 < E₀ →
      ∃ C' x₀ : ℝ, 0 < C' ∧ 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S →
          (∑ 𝒞 ∈ (constraintSystems (birthAddresses S.x K (memoryCutoff S))).filter
              (fun 𝒞 => (⌈C' * (S.N : ℝ) * Real.log S.L / Real.rpow S.L (1 / 10 : ℝ)⌉₊ ≤
                constraintRank 𝒞)),
            |(constraintCoeff 𝒞 : ℝ)| *
              ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight 𝒞)‖) ≤
            Real.rpow S.L (-(E₀ + 3) * (S.N : ℝ)) := by
  sorry

/-- `t2:pd.history-rank-low` (new node) — PD 04:906-956.  A constraint system of rank `r` changes at
most `2r` operations: write each block indicator by circle orthogonality (mem:local-phases), attach
every phase at the operation where its prime is born (an equivariant multiplier of modulus `≤ 1`);
if every edge satisfies the signed bound `L^{-G}`, then
`|H_𝒞| ≤ C_K^{N+1} ‖𝐛‖² L^{-G(N-2r)} L^{2Cr}` (mem:low-rank-term) with the crude exponent `C` of
`ghost_edge_crude` and `‖𝐛‖² ≤ 2` (mem:boundary-norm). Correction from refutation lane
`sol-gate-b` supplies symmetric-memory edge bounds to this history estimate. -/
theorem history_rank_low (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ C_K Ccr x₀ : ℝ, 0 < C_K ∧ 0 < Ccr ∧ 2 ≤ x₀ ∧
        ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x → ∀ w : ArchRoot, w.InRegion S →
          ∀ G : ℝ, 0 < G →
            (∀ j : ℕ, j < S.N →
              MemOpNormLE_sym F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.full j)
                (Real.rpow S.L (-G))) →
            ∀ 𝒞 ∈ constraintSystems (birthAddresses S.x K (memoryCutoff S)),
              ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight 𝒞)‖ ≤
                2 * C_K ^ (S.N + 1) *
                  Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (constraintRank 𝒞 : ℝ))) *
                  Real.rpow S.L (2 * Ccr * (constraintRank 𝒞 : ℝ)) := by
  sorry

private theorem pd5_birth_arithmetic_threshold {K : ℕ} {C' eta C_K : ℝ}
    (hC' : 0 < C') (heta : 0 < eta) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      4 ≤ Real.log x ∧ 13 * (K : ℝ) ≤ Real.rpow (Real.log x) (1 / 2 : ℝ) ∧
      C_K ≤ Real.log x ∧ C_K ^ 2 ≤ Real.rpow (Real.log x) (1 / 2 : ℝ) ∧
      2 / eta ≤ Real.rpow (Real.log x) (1 / 2 : ℝ) ∧
      C' * Real.log (Real.log x) / Real.rpow (Real.log x) (1 / 10 : ℝ) ≤ eta / 2 := by
  have hLog : Tendsto (fun x : ℝ => Real.log x) atTop atTop := Real.tendsto_log_atTop
  have hHalf : Tendsto (fun x : ℝ => Real.rpow (Real.log x) (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp hLog
  have hRatio : Tendsto (fun t : ℝ => Real.log t / Real.rpow t (1 / 10 : ℝ))
      atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : 0 < (1 / 10 : ℝ))).tendsto_div_nhds_zero
  have hRatioX := hRatio.comp hLog
  have hSmallRatio : ∀ᶠ x : ℝ in atTop,
      Real.log (Real.log x) / Real.rpow (Real.log x) (1 / 10 : ℝ) < eta / (2 * C') :=
    (tendsto_order.1 hRatioX).2 _ (div_pos heta (mul_pos (by norm_num) hC'))
  have hSmall : ∀ᶠ x : ℝ in atTop,
      C' * Real.log (Real.log x) / Real.rpow (Real.log x) (1 / 10 : ℝ) ≤ eta / 2 := by
    filter_upwards [hSmallRatio] with x hx
    have hmul := mul_lt_mul_of_pos_left hx hC'
    have hEq : C' * (eta / (2 * C')) = eta / 2 := by
      field_simp [ne_of_gt hC']
    have hEq' : C' *
        (Real.log (Real.log x) / Real.rpow (Real.log x) (1 / 10 : ℝ)) =
          C' * Real.log (Real.log x) / Real.rpow (Real.log x) (1 / 10 : ℝ) := by ring
    rw [hEq'] at hmul
    rw [hEq] at hmul
    exact hmul.le
  have hFour : ∀ᶠ x : ℝ in atTop, 4 ≤ Real.log x := (Filter.tendsto_atTop.1 hLog) 4
  have hCLog : ∀ᶠ x : ℝ in atTop, C_K ≤ Real.log x :=
    (Filter.tendsto_atTop.1 hLog) C_K
  have hHalfBig : ∀ᶠ x : ℝ in atTop,
      max (13 * (K : ℝ)) (max (2 / eta) (C_K ^ 2)) ≤
        Real.rpow (Real.log x) (1 / 2 : ℝ) := by
    exact (Filter.tendsto_atTop.1 hHalf)
      (max (13 * (K : ℝ)) (max (2 / eta) (C_K ^ 2)))
  have hX2 : ∀ᶠ x : ℝ in atTop, 2 ≤ x :=
    Filter.eventually_atTop.2 ⟨2, fun x hx => hx⟩
  have hAll := hX2.and hFour |>.and hCLog |>.and hHalfBig |>.and hSmall
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 hAll
  have hx₀prop := hx₀ x₀ le_rfl
  rcases hx₀prop with ⟨⟨⟨⟨hx₀₂, hL4₀⟩, hLCK₀⟩, hHalfBig₀⟩, hLsmall₀⟩
  refine ⟨x₀, hx₀₂, ?_⟩
  intro x hx
  obtain ⟨⟨⟨⟨hx₂, hL4⟩, hLCK⟩, hHalfBig⟩, hLsmall⟩ := hx₀ x hx
  have hLCKsq : C_K ^ 2 ≤ Real.rpow (Real.log x) (1 / 2 : ℝ) :=
    (le_trans (le_max_right _ _) (le_max_right _ _)).trans hHalfBig
  have hLhalf : 2 / eta ≤ Real.rpow (Real.log x) (1 / 2 : ℝ) :=
    (le_trans (le_max_left _ _) (le_max_right _ _)).trans hHalfBig
  have hL13K : 13 * (K : ℝ) ≤ Real.rpow (Real.log x) (1 / 2 : ℝ) :=
    (le_max_left _ _).trans hHalfBig
  exact ⟨hL4, hL13K, hLCK,
    hLCKsq, hLhalf, hLsmall⟩

set_option maxHeartbeats 0 in
/-- `t2:pd.birth-distinctness` — PD 04:784-966.  REPLACES the frozen `birth_distinctness`.
Assembly: the truncated distinct history is `≤ L^{-(E₀+2)N}` uniformly in the root.
`birth_partition` (logs of truncated histories have distinct addresses in `birthAddresses`),
`history_rank_high`, and `history_rank_low` with `signed_edge` for `G > E₀ + 3`; since
`r₀/N = O(log L / L^{0.1})`, the low ranks sum to `L^{(-G+o(1))N}` (mem:low-rank). -/
theorem birth_distinctness (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) (q_d : ℝ)
    (eta psi : ℝ → ℝ) :
    ∀ E₀ : ℝ, 0 < E₀ → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ,
      ∀ (K : ℕ), K₀ ≤ K → ∀ (F : PDFix K), F.Valid → F.Has q_d A₀ eta psi →
        ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
          ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
            ∀ w : ArchRoot, w.InRegion S →
              ‖historyDistinctTrunc F S ρ w‖ ≤ Real.rpow S.L (-(E₀ + 2) * (S.N : ℝ)) := by
  intro E₀ hE₀
  let G : ℝ := E₀ + 8
  have hG : 0 < G := by dsimp [G]; linarith
  obtain ⟨A₀, hA₀, K₀, hSignedAll⟩ :=
    signed_edge δ c₁ c₂ hδ hc₁ q_d eta psi G hG
  refine ⟨A₀, hA₀, ?_⟩
  refine ⟨K₀, ?_⟩
  intro K hK F hF hHas ρ hρ
  obtain ⟨xEdge, hxEdge, hSigned⟩ := hSignedAll K hK F hF hHas ρ hρ
  obtain ⟨C', xHigh, hC', hxHigh, hHigh⟩ :=
    history_rank_high δ c₁ c₂ hδ hc₁ K F hF ρ hρ E₀ hE₀
  obtain ⟨C_K, Ccr, xLow, hC_K, hCcr, hxLow, hLow⟩ :=
    history_rank_low δ c₁ c₂ hδ hc₁ K F hF ρ hρ
  let Cbar : ℝ := max 1 C_K
  have hCbarOne : 1 ≤ Cbar := le_max_left _ _
  have hCbarPos : 0 < Cbar := lt_of_lt_of_le (by norm_num) hCbarOne
  have hCkLeBar : C_K ≤ Cbar := le_max_right _ _
  let D : ℝ := 2 * G + 2 * Ccr + 9
  have hD : 0 < D := by dsimp [D, G]; positivity
  let η : ℝ := 1 / (2 * D)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨xArith, hxArith, hArith⟩ :=
    pd5_birth_arithmetic_threshold (K := K) (C_K := Cbar) hC' hη
  let x₀ : ℝ := max xEdge (max xHigh (max xLow xArith))
  have hxEdge₀ : xEdge ≤ x₀ := by
    change xEdge ≤ max xEdge (max xHigh (max xLow xArith))
    exact le_max_left _ _
  have hxHigh₀ : xHigh ≤ x₀ := by
    change xHigh ≤ max xEdge (max xHigh (max xLow xArith))
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hxLow₀ : xLow ≤ x₀ := by
    change xLow ≤ max xEdge (max xHigh (max xLow xArith))
    exact le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hxArith₀ : xArith ≤ x₀ := by
    change xArith ≤ max xEdge (max xHigh (max xLow xArith))
    exact le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _))
  have hx₀ : 2 ≤ x₀ := by
    exact hxArith.trans hxArith₀
  refine ⟨x₀, hx₀, ?_⟩
  intro S hS hx₀S w hw
  have hxEdgeS : xEdge ≤ S.x := hxEdge₀.trans hx₀S
  have hxHighS : xHigh ≤ S.x := hxHigh₀.trans hx₀S
  have hxLowS : xLow ≤ S.x := hxLow₀.trans hx₀S
  have hxArithS : xArith ≤ S.x := hxArith₀.trans hx₀S
  have hScale := hArith S.x hxArithS
  rcases hScale with ⟨hx2, hL4, hLCbar, hLCbarSq, hLhalf, hSmall⟩
  have hEdgeS := hSigned S hS hxEdgeS w hw
  have hHighS := hHigh S hS hxHighS w hw
  have hLowS := hLow S hS hxLowS w hw G (by dsimp [G]; linarith) hEdgeS
  have hbox : {z : ℤ × ℤ | envBox S w z}.Finite := pd5_envBox_finite_of_valid hS hw
  let A : Finset (BirthAddress K) := birthAddresses S.x K (memoryCutoff S)
  have hPartition := pd5_memHistory_partition_sum F S ρ w (memoryCutoff S) A
    (by intro a ha; exact ha) hbox
  have hTarget :
      ‖historyDistinctTrunc F S ρ w‖ ≤
        ∑ C ∈ constraintSystems A,
          |(constraintCoeff C : ℝ)| *
            ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight C)‖ := by
    rw [historyDistinctTrunc, hPartition]
    calc
      ‖∑ C ∈ constraintSystems A,
          (constraintCoeff C : ℂ) *
            memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight C)‖ ≤
          ∑ C ∈ constraintSystems A,
            ‖(constraintCoeff C : ℂ) *
              memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight C)‖ :=
        norm_sum_le _ _
      _ = ∑ C ∈ constraintSystems A,
            |(constraintCoeff C : ℝ)| *
              ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight C)‖ := by
        apply Finset.sum_congr rfl
        intro C hC
        simp [norm_mul, Complex.norm_real]
  let r₀ : ℕ :=
    ⌈C' * (S.N : ℝ) * Real.log S.L / Real.rpow S.L (1 / 10 : ℝ)⌉₊
  let systems := constraintSystems A
  let highSystems := systems.filter (fun C => r₀ ≤ constraintRank C)
  let lowSystems := systems.filter (fun C => constraintRank C < r₀)
  have hHighBound :
      (∑ C ∈ highSystems,
        |(constraintCoeff C : ℝ)| *
          ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight C)‖) ≤
        Real.rpow S.L (-(E₀ + 3) * (S.N : ℝ)) := by
    simpa [highSystems, systems, r₀, A] using hHighS
  have hLowC {C : Finset (Finset (BirthAddress K))} (hC : C ∈ systems) :
      ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight C)‖ ≤
        2 * C_K ^ (S.N + 1) *
          Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (constraintRank C : ℝ))) *
          Real.rpow S.L (2 * Ccr * (constraintRank C : ℝ)) := by
    exact hLowS C hC
  have hLone : 1 ≤ S.L := le_trans (by norm_num) hx2
  have hLpos : 0 < S.L := lt_of_lt_of_le (by norm_num) hLone
  have hCount := pd5_scale_counting_bounds hLone
  rcases hCount with ⟨hM, hNupper, hNlower, hB⟩
  have hHalfOne : 1 ≤ Real.rpow S.L (1 / 2 : ℝ) := by
    calc
      1 = Real.rpow S.L 0 := by simp
      _ ≤ Real.rpow S.L (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
  have hMhalf : (S.M : ℝ) ≤ 2 * Real.rpow S.L (1 / 2 : ℝ) := by
    have hExpo := Real.rpow_le_rpow_of_exponent_le hLone
      (by norm_num : (1 / 100 : ℝ) ≤ 1 / 2)
    calc
      (S.M : ℝ) ≤ 2 * Real.rpow S.L (1 / 100 : ℝ) := hM
      _ ≤ 2 * Real.rpow S.L (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hExpo (by norm_num)
  have hNthree : (S.N : ℝ) ≤ 3 * Real.rpow S.L (1 / 2 : ℝ) := by
    nlinarith [hNupper, hHalfOne]
  have hNplusFour : (S.N : ℝ) + 1 ≤ 4 * Real.rpow S.L (1 / 2 : ℝ) := by
    nlinarith [hNthree, hHalfOne]
  have hLpow2 : S.L ^ 2 = Real.rpow S.L (2 : ℝ) := by
    exact (Real.rpow_natCast S.L 2).symm
  have hpowFive : Real.rpow S.L (1 / 2 : ℝ) * S.L ^ 2 =
      Real.rpow S.L (5 / 2 : ℝ) := by
    calc
      _ = Real.rpow S.L (1 / 2 : ℝ) * Real.rpow S.L (2 : ℝ) := by rw [hLpow2]
      _ = Real.rpow S.L ((1 / 2 : ℝ) + 2) := (Real.rpow_add hLpos _ _).symm
      _ = Real.rpow S.L (5 / 2 : ℝ) := by congr 1 <;> norm_num
  have hNposReal : 0 < (S.N : ℝ) := by
    have hNge : 1 ≤ (S.N : ℝ) := by
      exact le_trans hHalfOne hNlower
    linarith
  have hNgeOne : 1 ≤ (S.N : ℝ) := le_trans hHalfOne hNlower
  have hNpos : 0 < S.N := by exact_mod_cast hNposReal
  have hAddressNat := pd5_birthAddresses_card_le (x := S.x) K (memoryCutoff S)
  have hAddressReal : (A.card : ℝ) ≤
      (K : ℝ) * (S.M : ℝ) + (K : ℝ) * (S.N : ℝ) +
        (K : ℝ) * ((S.N : ℝ) + 1) * (memoryCutoff S : ℝ) := by
    exact_mod_cast hAddressNat
  have hKnonneg : 0 ≤ (K : ℝ) := Nat.cast_nonneg _
  have hFirstCard : (K : ℝ) * (S.M : ℝ) ≤
      2 * (K : ℝ) * Real.rpow S.L (1 / 2 : ℝ) := by
    calc
      (K : ℝ) * (S.M : ℝ) ≤ (K : ℝ) * (2 * Real.rpow S.L (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hMhalf hKnonneg
      _ = 2 * (K : ℝ) * Real.rpow S.L (1 / 2 : ℝ) := by ring
  have hSecondCard : (K : ℝ) * (S.N : ℝ) ≤
      3 * (K : ℝ) * Real.rpow S.L (1 / 2 : ℝ) := by
    calc
      (K : ℝ) * (S.N : ℝ) ≤ (K : ℝ) * (3 * Real.rpow S.L (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hNthree hKnonneg
      _ = 3 * (K : ℝ) * Real.rpow S.L (1 / 2 : ℝ) := by ring
  have hThirdCard : (K : ℝ) * ((S.N : ℝ) + 1) * (memoryCutoff S : ℝ) ≤
      8 * (K : ℝ) * Real.rpow S.L (5 / 2 : ℝ) := by
    have hprod := mul_le_mul hNplusFour hB (by positivity) (by positivity)
    have hprodK := mul_le_mul_of_nonneg_left hprod hKnonneg
    calc
      (K : ℝ) * ((S.N : ℝ) + 1) * (memoryCutoff S : ℝ) =
          (K : ℝ) * (((S.N : ℝ) + 1) * (memoryCutoff S : ℝ)) := by ring
      _ ≤ (K : ℝ) * ((4 * Real.rpow S.L (1 / 2 : ℝ)) * (2 * S.L ^ 2)) := hprodK
      _ = 8 * (K : ℝ) * (Real.rpow S.L (1 / 2 : ℝ) * S.L ^ 2) := by ring
      _ = 8 * (K : ℝ) * Real.rpow S.L (5 / 2 : ℝ) := by
        rw [hpowFive]
  have hHalfFive : Real.rpow S.L (1 / 2 : ℝ) ≤ Real.rpow S.L (5 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
  have hCardBound : (A.card : ℝ) ≤
      13 * (K : ℝ) * Real.rpow S.L (5 / 2 : ℝ) := by
    calc
      (A.card : ℝ) ≤
          (K : ℝ) * (S.M : ℝ) + (K : ℝ) * (S.N : ℝ) +
            (K : ℝ) * ((S.N : ℝ) + 1) * (memoryCutoff S : ℝ) := hAddressReal
      _ ≤ 2 * (K : ℝ) * Real.rpow S.L (1 / 2 : ℝ) +
            3 * (K : ℝ) * Real.rpow S.L (1 / 2 : ℝ) +
            8 * (K : ℝ) * Real.rpow S.L (5 / 2 : ℝ) := by
          exact add_le_add (add_le_add hFirstCard hSecondCard) hThirdCard
      _ ≤ 13 * (K : ℝ) * Real.rpow S.L (5 / 2 : ℝ) := by
          have h2 := mul_le_mul_of_nonneg_left hHalfFive (by positivity : 0 ≤ 2 * (K : ℝ))
          have h3 := mul_le_mul_of_nonneg_left hHalfFive (by positivity : 0 ≤ 3 * (K : ℝ))
          calc
            _ ≤ 2 * (K : ℝ) * Real.rpow S.L (5 / 2 : ℝ) +
                3 * (K : ℝ) * Real.rpow S.L (5 / 2 : ℝ) +
                8 * (K : ℝ) * Real.rpow S.L (5 / 2 : ℝ) :=
              add_le_add (add_le_add h2 h3) le_rfl
            _ = 13 * (K : ℝ) * Real.rpow S.L (5 / 2 : ℝ) := by ring
  have hCard : (A.card : ℝ) ≤ Real.rpow S.L 3 := by
    calc
      (A.card : ℝ) ≤ 13 * (K : ℝ) * Real.rpow S.L (5 / 2 : ℝ) := hCardBound
      _ ≤ Real.rpow S.L (1 / 2 : ℝ) * Real.rpow S.L (5 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hL4
          (Real.rpow_nonneg hLpos.le _)
      _ = Real.rpow S.L ((1 / 2 : ℝ) + (5 / 2 : ℝ)) :=
        (Real.rpow_add hLpos _ _).symm
      _ = Real.rpow S.L 3 := by congr 1 <;> norm_num
  have hCardMax : (max 1 A.card : ℝ) ≤ Real.rpow S.L 3 := by
    change max (1 : ℝ) (A.card : ℝ) ≤ Real.rpow S.L 3
    apply max_le
    · calc
        1 = Real.rpow S.L 0 := by simp
        _ ≤ Real.rpow S.L 3 := Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
    · exact hCard
  have hDhalf : 1 / 2 ≤ D := by
    change 1 / 2 ≤ 2 * G + 2 * Ccr + 9
    calc
      1 / 2 ≤ 9 := by norm_num
      _ ≤ 2 * G + 2 * Ccr + 9 := by nlinarith [hG, hCcr]
  have hEtaLeOne : η ≤ 1 := by
    have hDen : 0 < 2 * D := by positivity
    dsimp [η]
    rw [div_le_iff₀ hDen]
    nlinarith [hDhalf]
  have hNeta : 2 / η ≤ (S.N : ℝ) := le_trans hLhalf hNlower
  have hInvN : 1 / (S.N : ℝ) ≤ η / 2 := by
    apply (div_le_iff₀ hNposReal).2
    have hmul := mul_le_mul_of_nonneg_left hNeta (by positivity : 0 ≤ η / 2)
    have hmul' : 1 ≤ (η / 2) * (S.N : ℝ) := by
      have heq : (η / 2) * (2 / η) = 1 := by field_simp [ne_of_gt hη]
      rw [heq] at hmul
      exact hmul
    nlinarith [hmul']
  have hLge4 : 4 ≤ S.L := by simpa [PDScale.L] using hx2
  have hLogLpos : 0 < Real.log S.L := Real.log_pos (by linarith [hLge4])
  have hCeilUpper : (r₀ : ℝ) <
      C' * (S.N : ℝ) * Real.log S.L / Real.rpow S.L (1 / 10 : ℝ) + 1 := by
    dsimp [r₀]
    exact Nat.ceil_lt_add_one (by positivity)
  have hSmallL : C' * Real.log S.L / Real.rpow S.L (1 / 10 : ℝ) ≤ η / 2 := by
    simpa [PDScale.L] using hSmall
  have hR₀div : (r₀ : ℝ) / (S.N : ℝ) ≤ η := by
    have hDiv : (r₀ : ℝ) / (S.N : ℝ) <
        C' * Real.log S.L / Real.rpow S.L (1 / 10 : ℝ) + 1 / (S.N : ℝ) := by
      calc
        _ < (C' * (S.N : ℝ) * Real.log S.L /
            Real.rpow S.L (1 / 10 : ℝ) + 1) / (S.N : ℝ) :=
              div_lt_div_of_pos_right hCeilUpper hNposReal
        _ = _ := by
          field_simp [ne_of_gt hNposReal,
            ne_of_gt (Real.rpow_pos_of_pos hLpos (1 / 10 : ℝ))]
    calc
      (r₀ : ℝ) / (S.N : ℝ) ≤
          C' * Real.log S.L / Real.rpow S.L (1 / 10 : ℝ) + 1 / (S.N : ℝ) := hDiv.le
      _ ≤ η / 2 + η / 2 := add_le_add hSmallL hInvN
      _ = η := by ring
  have hR₀leNreal : (r₀ : ℝ) ≤ (S.N : ℝ) := by
    have hR₀divOne := hR₀div.trans hEtaLeOne
    have hmul := (div_le_iff₀ hNposReal).1 hR₀divOne
    simpa using hmul
  have hR₀leN : r₀ ≤ S.N := by exact_mod_cast hR₀leNreal
  have hDr₀ : D * (r₀ : ℝ) ≤ (S.N : ℝ) / 2 := by
    have hmul := mul_le_mul_of_nonneg_left
      ((div_le_iff₀ hNposReal).1 hR₀div) hD.le
    have hEtaD : η * D = 1 / 2 := by dsimp [η]; field_simp [ne_of_gt hD]
    nlinarith [hmul, hEtaD]
  have hSqrtLeL : Real.rpow S.L (1 / 2 : ℝ) ≤ S.L := by
    calc
      Real.rpow S.L (1 / 2 : ℝ) ≤ Real.rpow S.L 1 :=
        Real.rpow_le_rpow_of_exponent_le hLone (by norm_num)
      _ = S.L := Real.rpow_one _
  have hNleL2 : 2 * (S.N : ℝ) ≤ S.L ^ 2 := by
    have hNle : (S.N : ℝ) ≤ S.L + 2 := by nlinarith [hNupper, hSqrtLeL]
    nlinarith [hNle, sq_nonneg (S.L - 3), hLge4]
  have hTwoNleL2 : 2 * (r₀ : ℝ) ≤ S.L ^ 2 := by
    exact le_trans (by nlinarith [hR₀leNreal]) hNleL2
  let f : Finset (Finset (BirthAddress K)) → ℝ := fun C =>
    |(constraintCoeff C : ℝ)| *
      ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight C)‖
  have hLowGrouped :
      (∑ C ∈ lowSystems, f C) =
        ∑ r ∈ Finset.range r₀,
          ∑ C ∈ (constraintSystems A).filter (fun C => constraintRank C = r), f C := by
    simpa [lowSystems, systems] using
      pd5_constraint_sum_group_by_rank A r₀ f
  have hMassPower (r : ℕ) :
      (max 1 A.card : ℝ) ^ (3 * r) ≤ Real.rpow S.L (9 * (r : ℝ)) := by
    calc
      (max 1 A.card : ℝ) ^ (3 * r) ≤ (Real.rpow S.L 3) ^ (3 * r) :=
        pow_le_pow_left₀ (by positivity) hCardMax _
      _ = Real.rpow S.L (9 * (r : ℝ)) := by
        have hL3 : Real.rpow S.L (3 : ℝ) = S.L ^ 3 := Real.rpow_natCast S.L 3
        calc
          (Real.rpow S.L 3) ^ (3 * r) = (S.L ^ 3) ^ (3 * r) := by rw [hL3]
          _ = S.L ^ (9 * r) := by
            rw [← pow_mul]
            congr 1
            omega
          _ = Real.rpow S.L (9 * (r : ℝ)) := by
            calc
              S.L ^ (9 * r) = Real.rpow S.L ((9 * r : ℕ) : ℝ) :=
                (Real.rpow_natCast S.L (9 * r)).symm
              _ = Real.rpow S.L (9 * (r : ℝ)) := by congr 1; push_cast; ring
  have hExponent (r : ℕ) :
      Real.rpow S.L (9 * (r : ℝ)) *
          Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (r : ℝ))) *
          Real.rpow S.L (2 * Ccr * (r : ℝ)) =
        Real.rpow S.L (-G * (S.N : ℝ) + D * (r : ℝ)) := by
    calc
      _ = (Real.rpow S.L (9 * (r : ℝ)) *
            Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (r : ℝ)))) *
            Real.rpow S.L (2 * Ccr * (r : ℝ)) := by ring
      _ = Real.rpow S.L (9 * (r : ℝ) +
            (-G * ((S.N : ℝ) - 2 * (r : ℝ)))) *
            Real.rpow S.L (2 * Ccr * (r : ℝ)) :=
          congrArg (fun t : ℝ => t * Real.rpow S.L (2 * Ccr * (r : ℝ)))
            (Real.rpow_add hLpos _ _).symm
      _ = Real.rpow S.L
            (9 * (r : ℝ) + (-G * ((S.N : ℝ) - 2 * (r : ℝ))) +
              2 * Ccr * (r : ℝ)) := (Real.rpow_add hLpos _ _).symm
      _ = Real.rpow S.L (-G * (S.N : ℝ) + D * (r : ℝ)) := by
        congr 1
        dsimp [D]
        ring
  have hRankBound (r : ℕ) (hr : r < r₀) :
      (∑ C ∈ (constraintSystems A).filter (fun C => constraintRank C = r), f C) ≤
        2 * Cbar ^ (S.N + 1) *
          Real.rpow S.L (-G * (S.N : ℝ) + (S.N : ℝ) / 2) := by
    let R := (constraintSystems A).filter (fun C => constraintRank C = r)
    have hCbarPow : C_K ^ (S.N + 1) ≤ Cbar ^ (S.N + 1) :=
      pow_le_pow_left₀ (le_of_lt hC_K) hCkLeBar _
    have hrReal : (r : ℝ) ≤ (r₀ : ℝ) := by exact_mod_cast hr.le
    have hDr : D * (r : ℝ) ≤ (S.N : ℝ) / 2 := by
      calc
        D * (r : ℝ) ≤ D * (r₀ : ℝ) := mul_le_mul_of_nonneg_left hrReal hD.le
        _ ≤ (S.N : ℝ) / 2 := hDr₀
    have hExpLe : -G * (S.N : ℝ) + D * (r : ℝ) ≤
        -G * (S.N : ℝ) + (S.N : ℝ) / 2 :=
      add_le_add le_rfl hDr
    have hRpow1 : 0 ≤
        Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (r : ℝ))) :=
      Real.rpow_nonneg hLpos.le _
    have hRpow2 : 0 ≤ Real.rpow S.L (2 * Ccr * (r : ℝ)) :=
      Real.rpow_nonneg hLpos.le _
    have hRpowProd : 0 ≤
        Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (r : ℝ))) *
          Real.rpow S.L (2 * Ccr * (r : ℝ)) := mul_nonneg hRpow1 hRpow2
    have hFullFactor : 0 ≤ 2 * Cbar ^ (S.N + 1) *
        Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (r : ℝ))) *
        Real.rpow S.L (2 * Ccr * (r : ℝ)) := by
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hCbarPos.le _)) hRpow1)
        hRpow2
    have hMass := pd5_constraint_coeff_mass_le A r
    calc
      (∑ C ∈ R, f C) ≤
          ∑ C ∈ R,
            |(constraintCoeff C : ℝ)| *
              (2 * Cbar ^ (S.N + 1) *
                Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (r : ℝ))) *
                Real.rpow S.L (2 * Ccr * (r : ℝ))) := by
        apply Finset.sum_le_sum
        intro C hCR
        have hCS : C ∈ systems := (Finset.mem_filter.mp hCR).1
        have hNorm := hLowC hCS
        have hNormBar :
            ‖memHistory F S ρ w (some (memoryCutoff S)) none (constraintWeight C)‖ ≤
              2 * Cbar ^ (S.N + 1) *
                Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (r : ℝ))) *
                Real.rpow S.L (2 * Ccr * (r : ℝ)) := by
          calc
            _ ≤ 2 * C_K ^ (S.N + 1) *
                Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (constraintRank C : ℝ))) *
                Real.rpow S.L (2 * Ccr * (constraintRank C : ℝ)) := hNorm
            _ = 2 * C_K ^ (S.N + 1) *
                Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (r : ℝ))) *
                Real.rpow S.L (2 * Ccr * (r : ℝ)) := by
                  rw [(Finset.mem_filter.mp hCR).2]
            _ ≤ 2 * Cbar ^ (S.N + 1) *
                Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (r : ℝ))) *
                Real.rpow S.L (2 * Ccr * (r : ℝ)) := by
                  have hbase := mul_le_mul_of_nonneg_left hCbarPow (by norm_num : 0 ≤ (2 : ℝ))
                  calc
                    _ = (2 * C_K ^ (S.N + 1)) *
                        (Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (r : ℝ))) *
                          Real.rpow S.L (2 * Ccr * (r : ℝ))) := by ring
                    _ ≤ (2 * Cbar ^ (S.N + 1)) *
                        (Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (r : ℝ))) *
                          Real.rpow S.L (2 * Ccr * (r : ℝ))) :=
                      mul_le_mul_of_nonneg_right hbase hRpowProd
                    _ = _ := by ring
        exact mul_le_mul_of_nonneg_left hNormBar (abs_nonneg _)
      _ = (∑ C ∈ R, |(constraintCoeff C : ℝ)|) *
          (2 * Cbar ^ (S.N + 1) *
            Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (r : ℝ))) *
            Real.rpow S.L (2 * Ccr * (r : ℝ))) := by
        rw [← Finset.sum_mul]
      _ ≤ (max 1 A.card : ℝ) ^ (3 * r) *
          (2 * Cbar ^ (S.N + 1) *
            Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (r : ℝ))) *
            Real.rpow S.L (2 * Ccr * (r : ℝ))) :=
        mul_le_mul_of_nonneg_right hMass hFullFactor
      _ ≤ Real.rpow S.L (9 * (r : ℝ)) *
          (2 * Cbar ^ (S.N + 1) *
            Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (r : ℝ))) *
            Real.rpow S.L (2 * Ccr * (r : ℝ))) :=
        mul_le_mul_of_nonneg_right (hMassPower r) hFullFactor
      _ = 2 * Cbar ^ (S.N + 1) *
          Real.rpow S.L (-G * (S.N : ℝ) + D * (r : ℝ)) := by
        calc
          _ = 2 * Cbar ^ (S.N + 1) *
              (Real.rpow S.L (9 * (r : ℝ)) *
                Real.rpow S.L (-G * ((S.N : ℝ) - 2 * (r : ℝ))) *
                Real.rpow S.L (2 * Ccr * (r : ℝ))) := by ring
          _ = _ := by rw [hExponent r]
      _ ≤ 2 * Cbar ^ (S.N + 1) *
          Real.rpow S.L (-G * (S.N : ℝ) + (S.N : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hLone hExpLe) (by positivity)
  have hLowAll : (∑ C ∈ lowSystems, f C) ≤
      (r₀ : ℝ) *
        (2 * Cbar ^ (S.N + 1) *
          Real.rpow S.L (-G * (S.N : ℝ) + (S.N : ℝ) / 2)) := by
    rw [hLowGrouped]
    calc
      _ ≤ ∑ r ∈ Finset.range r₀,
          2 * Cbar ^ (S.N + 1) *
            Real.rpow S.L (-G * (S.N : ℝ) + (S.N : ℝ) / 2) := by
        apply Finset.sum_le_sum
        intro r hr
        exact hRankBound r (Finset.mem_range.mp hr)
      _ = (r₀ : ℝ) *
          (2 * Cbar ^ (S.N + 1) *
            Real.rpow S.L (-G * (S.N : ℝ) + (S.N : ℝ) / 2)) := by simp
  have hCbarGrowth : Cbar ^ (S.N + 1) ≤ Real.rpow S.L ((S.N : ℝ) / 2) := by
    have hNatExp : S.N + 1 ≤ 2 * S.N := by omega
    calc
      Cbar ^ (S.N + 1) ≤ Cbar ^ (2 * S.N) := pow_le_pow_right₀ hCbarOne hNatExp
      _ = (Cbar ^ 2) ^ S.N := by rw [pow_mul]
      _ ≤ (Real.rpow S.L (1 / 2 : ℝ)) ^ S.N :=
        pow_le_pow_left₀ (by positivity) hLCbarSq _
      _ = Real.rpow S.L ((S.N : ℝ) / 2) := by
        calc
          (Real.rpow S.L (1 / 2 : ℝ)) ^ S.N =
              Real.rpow (Real.rpow S.L (1 / 2 : ℝ)) (S.N : ℝ) :=
            (Real.rpow_natCast _ _).symm
          _ = Real.rpow S.L ((1 / 2 : ℝ) * (S.N : ℝ)) :=
            (Real.rpow_mul hLpos.le _ _).symm
          _ = Real.rpow S.L ((S.N : ℝ) / 2) := by congr 1; ring
  have hLowBound : (∑ C ∈ lowSystems, f C) ≤
      Real.rpow S.L (-(E₀ + 3) * (S.N : ℝ)) := by
    have hCoeff :
        2 * (r₀ : ℝ) * Cbar ^ (S.N + 1) ≤
          S.L ^ 2 * Real.rpow S.L ((S.N : ℝ) / 2) := by
      calc
        2 * (r₀ : ℝ) * Cbar ^ (S.N + 1) ≤
            S.L ^ 2 * Cbar ^ (S.N + 1) := by
          exact mul_le_mul_of_nonneg_right hTwoNleL2 (by positivity)
        _ ≤ S.L ^ 2 * Real.rpow S.L ((S.N : ℝ) / 2) :=
          mul_le_mul_of_nonneg_left hCbarGrowth (by positivity)
    have hFinalExp : 2 + (S.N : ℝ) / 2 +
        (-G * (S.N : ℝ) + (S.N : ℝ) / 2) ≤ -(E₀ + 3) * (S.N : ℝ) := by
      dsimp [G]
      nlinarith [hNgeOne]
    calc
      (∑ C ∈ lowSystems, f C) ≤
          (r₀ : ℝ) *
            (2 * Cbar ^ (S.N + 1) *
              Real.rpow S.L (-G * (S.N : ℝ) + (S.N : ℝ) / 2)) := hLowAll
      _ = (2 * (r₀ : ℝ) * Cbar ^ (S.N + 1)) *
          Real.rpow S.L (-G * (S.N : ℝ) + (S.N : ℝ) / 2) := by ring
      _ ≤ (S.L ^ 2 * Real.rpow S.L ((S.N : ℝ) / 2)) *
          Real.rpow S.L (-G * (S.N : ℝ) + (S.N : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right hCoeff
          (Real.rpow_nonneg hLpos.le _)
      _ = Real.rpow S.L 2 * Real.rpow S.L ((S.N : ℝ) / 2) *
          Real.rpow S.L (-G * (S.N : ℝ) + (S.N : ℝ) / 2) := by
        rw [hLpow2]
      _ = Real.rpow S.L (2 + (S.N : ℝ) / 2) *
          Real.rpow S.L (-G * (S.N : ℝ) + (S.N : ℝ) / 2) :=
        (Real.rpow_add hLpos 2 ((S.N : ℝ) / 2)).symm ▸ rfl
      _ = Real.rpow S.L
          (2 + (S.N : ℝ) / 2 + (-G * (S.N : ℝ) + (S.N : ℝ) / 2)) :=
        (Real.rpow_add hLpos (2 + (S.N : ℝ) / 2)
          (-G * (S.N : ℝ) + (S.N : ℝ) / 2)).symm
      _ ≤ Real.rpow S.L (-(E₀ + 3) * (S.N : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hLone hFinalExp
  have hSplit : (∑ C ∈ systems, f C) =
      (∑ C ∈ highSystems, f C) + (∑ C ∈ lowSystems, f C) := by
    simpa [highSystems, lowSystems, systems, not_le] using
      (Finset.sum_filter_add_sum_filter_not systems
        (fun C => r₀ ≤ constraintRank C) f).symm
  have hTwoLeNPower : 2 ≤ Real.rpow S.L (S.N : ℝ) := by
    calc
      2 ≤ S.L := by linarith [hLge4]
      _ = Real.rpow S.L 1 := (Real.rpow_one _).symm
      _ ≤ Real.rpow S.L (S.N : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hLone hNgeOne
  have hCombine :
      2 * Real.rpow S.L (-(E₀ + 3) * (S.N : ℝ)) ≤
        Real.rpow S.L (-(E₀ + 2) * (S.N : ℝ)) := by
    calc
      2 * Real.rpow S.L (-(E₀ + 3) * (S.N : ℝ)) ≤
          Real.rpow S.L (S.N : ℝ) *
            Real.rpow S.L (-(E₀ + 3) * (S.N : ℝ)) :=
        mul_le_mul_of_nonneg_right hTwoLeNPower
          (Real.rpow_nonneg hLpos.le _)
      _ = Real.rpow S.L
          ((S.N : ℝ) + (-(E₀ + 3) * (S.N : ℝ))) :=
        (Real.rpow_add hLpos _ _).symm
      _ = Real.rpow S.L (-(E₀ + 2) * (S.N : ℝ)) := by
        congr 1
        ring
  calc
    ‖historyDistinctTrunc F S ρ w‖ ≤ ∑ C ∈ systems, f C := by
      simpa [f] using hTarget
    _ = (∑ C ∈ highSystems, f C) + (∑ C ∈ lowSystems, f C) := hSplit
    _ ≤ Real.rpow S.L (-(E₀ + 3) * (S.N : ℝ)) +
        Real.rpow S.L (-(E₀ + 3) * (S.N : ℝ)) :=
      add_le_add hHighBound hLowBound
    _ = 2 * Real.rpow S.L (-(E₀ + 3) * (S.N : ℝ)) := by ring
    _ ≤ Real.rpow S.L (-(E₀ + 2) * (S.N : ℝ)) := hCombine

/-! ## §6 Removing goodness, stripping pads, Proposition 4.1 (PD 04:968-1117, 11-35) -/

/-- The scale of a coefficient family at `x` with selected-product scale `Y` and pad `d₀`. -/
def familyScale {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (x Y : ℝ) (d₀ : ℕ) :
    PDScale := ⟨x, family.Hm x, family.Hn x, Y, d₀⟩

/-- `β` hypotheses at the family's second dyad. -/
def IsFamilySecondCoefficient {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (x : ℝ)
    (beta : ℕ → ℂ) : Prop :=
  (∀ n, beta n ≠ 0 → n ∈ dyadicIntegers (family.Hn x) ∧ roughAbove n (roughCutoff x)) ∧
    ∀ n ∈ dyadicIntegers (family.Hn x), ‖beta n‖ ≤ Real.rpow (Real.log x) C

/-- A stretched exponential absorbs every fixed power of the logarithmic scale. -/
private theorem logPower_expDecay (A B c : ℝ) (hc : 0 < c) :
    ∃ L₀ : ℝ, 1 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      Real.rpow L B * Real.exp (-c * Real.rpow L (1 / 10 : ℝ)) ≤
        Real.rpow L (-A) := by
  have hpowTendsto : Filter.Tendsto (fun L : ℝ => Real.rpow L (1 / 10 : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_rpow_atTop (y := (1 / 10 : ℝ)) (by norm_num)
  have hcomp :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10 * (A + B)) c hc).comp hpowTendsto
  have heq : (fun L : ℝ =>
      Real.rpow (Real.rpow L (1 / 10 : ℝ)) (10 * (A + B)) *
        Real.exp (-c * Real.rpow L (1 / 10 : ℝ))) =ᶠ[Filter.atTop]
      (fun L : ℝ => Real.rpow L (A + B) *
        Real.exp (-c * Real.rpow L (1 / 10 : ℝ))) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with L hL
    have hpower : Real.rpow (Real.rpow L (1 / 10 : ℝ)) (10 * (A + B)) =
        Real.rpow L (A + B) := by
      have hlogpow : Real.log (Real.rpow L (1 / 10 : ℝ)) =
          (1 / 10 : ℝ) * Real.log L := by
        change Real.log (L ^ (1 / 10 : ℝ)) = _
        exact Real.log_rpow hL _
      calc
        Real.rpow (Real.rpow L (1 / 10 : ℝ)) (10 * (A + B)) =
            Real.exp (Real.log (Real.rpow L (1 / 10 : ℝ)) * (10 * (A + B))) :=
              Real.rpow_def_of_pos (Real.rpow_pos_of_pos hL _) _
        _ = Real.exp (Real.log L * (A + B)) := by
          rw [hlogpow]
          congr 1
          ring
        _ = Real.rpow L (A + B) := (Real.rpow_def_of_pos hL _).symm
    rw [hpower]
  have hlim : Filter.Tendsto (fun L : ℝ =>
      Real.rpow L (A + B) * Real.exp (-c * Real.rpow L (1 / 10 : ℝ)))
        Filter.atTop (nhds 0) :=
    hcomp.congr' heq
  have hevent : ∀ᶠ L : ℝ in Filter.atTop,
      Real.rpow L (A + B) * Real.exp (-c * Real.rpow L (1 / 10 : ℝ)) < 1 :=
    hlim.eventually (Iio_mem_nhds (by norm_num))
  rcases Filter.eventually_atTop.mp hevent with ⟨L₁, hL₁⟩
  refine ⟨max 1 L₁, le_max_left _ _, ?_⟩
  intro L hL
  have hL₀ : L₁ ≤ L := le_trans (le_max_right _ _) hL
  have hLone : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hLone
  have hsmall := (hL₁ L hL₀).le
  have hpow : Real.rpow L (-A) * Real.rpow L (A + B) = Real.rpow L B := by
    calc
      Real.rpow L (-A) * Real.rpow L (A + B) = Real.rpow L (-A + (A + B)) :=
        (Real.rpow_add hLpos _ _).symm
      _ = Real.rpow L B := by congr 1 <;> ring
  calc
    Real.rpow L B * Real.exp (-c * Real.rpow L (1 / 10 : ℝ)) =
        Real.rpow L (-A) *
          (Real.rpow L (A + B) * Real.exp (-c * Real.rpow L (1 / 10 : ℝ))) := by
            rw [← hpow]
            ring
    _ ≤ Real.rpow L (-A) * 1 := mul_le_mul_of_nonneg_left hsmall
      (Real.rpow_nonneg (le_of_lt hLpos) _)
    _ = Real.rpow L (-A) := by ring

/-- Two fixed marked prime bands are disjoint once the larger exponent separates their endpoints. -/
private theorem primeBand_disjoint_eventually (a b : ℝ) (hab : a < b) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → Disjoint (primeBand x a) (primeBand x b) := by
  have hpow : Filter.Tendsto (fun x : ℝ => Real.rpow (Real.log x) (b - a))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hab)).comp Real.tendsto_log_atTop
  have hevent : ∀ᶠ x : ℝ in Filter.atTop, 2 < Real.rpow (Real.log x) (b - a) :=
    hpow.eventually_gt_atTop 2
  rcases Filter.eventually_atTop.mp hevent with ⟨x₁, hx₁⟩
  refine ⟨max 2 x₁, le_max_left _ _, ?_⟩
  intro x hx
  have hx₂ : 2 ≤ x := le_trans (le_max_left _ _) hx
  have hgap : 2 < Real.rpow (Real.log x) (b - a) := hx₁ x (le_trans (le_max_right _ _) hx)
  have hLpos : 0 < Real.log x := Real.log_pos (by linarith)
  have hpa : 0 < Real.rpow (Real.log x) a := Real.rpow_pos_of_pos hLpos a
  have hpowMul : Real.rpow (Real.log x) b =
      Real.rpow (Real.log x) a * Real.rpow (Real.log x) (b - a) := by
    calc
      Real.rpow (Real.log x) b = Real.rpow (Real.log x) (a + (b - a)) := by congr 1 <;> ring
      _ = Real.rpow (Real.log x) a * Real.rpow (Real.log x) (b - a) :=
        Real.rpow_add hLpos _ _
  have hsep : 2 * Real.rpow (Real.log x) a < Real.rpow (Real.log x) b := by
    rw [hpowMul]
    nlinarith [mul_lt_mul_of_pos_left hgap hpa]
  apply Finset.disjoint_left.mpr
  intro p hp hq
  rcases Finset.mem_filter.mp hp with ⟨_, ⟨_, _, hpupper⟩⟩
  rcases Finset.mem_filter.mp hq with ⟨_, ⟨_, hqlower, _⟩⟩
  have hexp : Real.exp (2 * Real.rpow (Real.log x) a) <
      Real.exp (Real.rpow (Real.log x) b) := Real.exp_lt_exp.mpr hsep
  have hupper' : (p : ℝ) < Real.exp (Real.rpow (Real.log x) b) := lt_of_le_of_lt hpupper hexp
  linarith

/-- Valid ordered band data give one threshold at which all distinct marked bands are disjoint. -/
private theorem validBands_disjoint_eventually (K : ℕ) (a : Fin K → ℝ)
    (ha : ValidBands K a) :
    ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ i j : Fin K, i ≠ j →
      Disjoint (primeBand x (a i)) (primeBand x (a j)) := by
  have hevent : ∀ᶠ x : ℝ in Filter.atTop, ∀ ij : Fin K × Fin K,
      ij.1 = ij.2 ∨ Disjoint (primeBand x (a ij.1)) (primeBand x (a ij.2)) := by
    rw [Filter.eventually_all]
    intro ij
    by_cases hij : ij.1 = ij.2
    · exact Filter.Eventually.of_forall fun _ => Or.inl hij
    · rcases lt_or_gt_of_ne hij with hlt | hgt
      · have hab : a ij.1 < a ij.2 := ha.2.2 _ _ hlt
        obtain ⟨x₁, hx₁₂, hdis⟩ := primeBand_disjoint_eventually (a ij.1) (a ij.2) hab
        filter_upwards [Filter.eventually_ge_atTop x₁] with x hx
        exact Or.inr (hdis x hx)
      · have hab : a ij.2 < a ij.1 := ha.2.2 _ _ hgt
        obtain ⟨x₁, hx₁₂, hdis⟩ := primeBand_disjoint_eventually (a ij.2) (a ij.1) hab
        filter_upwards [Filter.eventually_ge_atTop x₁] with x hx
        exact Or.inr (disjoint_comm.mp (hdis x hx))
  rcases Filter.eventually_atTop.mp hevent with ⟨x₁, hx₁⟩
  refine ⟨max 2 x₁, le_max_left _ _, ?_⟩
  intro x hx i j hij
  have hxpair := hx₁ x (le_trans (le_max_right _ _) hx) (i, j)
  rcases hxpair with heq | hdis
  · exact (hij heq).elim
  · exact hdis

/-- A valid prime list has squarefree total product once its distinct marked bands are disjoint. -/
private theorem primeListProduct_squarefree {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (p : PrimeLists x K) (hp : ValidPrimeLists x K a p)
    (hbands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j))) :
    Squarefree (∏ i : Fin K, ∏ j : Fin (slotCount x), p i j) := by
  let f : Fin K × Fin (slotCount x) → ℕ := fun ij => p ij.1 ij.2
  have hpair : Set.Pairwise (↑(Finset.univ : Finset (Fin K × Fin (slotCount x))))
      (Function.onFun IsRelPrime f) := by
    intro ij _ ij' _ hne
    have hprime := (hp.1 ij.1 ij.2).1
    have hprime' := (hp.1 ij'.1 ij'.2).1
    have hlabels : p ij.1 ij.2 ≠ p ij'.1 ij'.2 := by
      intro heq
      have hgroup : ij.1 = ij'.1 := by
        by_contra hgroup
        have hdis := hbands ij.1 ij'.1 hgroup
        have hnot : p ij.1 ij.2 ∉ primeBand x (a ij'.1) :=
          (Finset.disjoint_left.mp hdis) (hp.1 ij.1 ij.2).2
        have hmem : p ij.1 ij.2 ∈ primeBand x (a ij'.1) := by
          simpa [heq] using (hp.1 ij'.1 ij'.2).2
        exact hnot hmem
      have hslot : ij.2 = ij'.2 := by
        by_contra hslot
        have hdiff := hp.2 ij.1 ij.2 ij'.2 hslot
        apply hdiff
        simpa [hgroup] using heq
      exact hne (Prod.ext hgroup hslot)
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes hprime hprime').2 hlabels)
  have hprod := Finset.squarefree_prod_of_pairwise_isCoprime (s := Finset.univ) hpair
    (fun (ij : Fin K × Fin (slotCount x)) _ => (hp.1 ij.1 ij.2).1.squarefree)
  simpa [f, Fintype.prod_prod_type] using hprod

/-- The product of a valid label list is subexponential in the root-line modulus range. -/
private theorem primeListProduct_le_exp {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (ha : ValidBands K a) (p : PrimeLists x K) (hp : ValidPrimeLists x K a p)
    (hL : 1 ≤ Real.log x) :
    (∏ i : Fin K, ∏ j : Fin (slotCount x), (p i j : ℝ)) ≤
      Real.exp (4 * (K : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ)) := by
  let L : ℝ := Real.log x
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hLpow : 1 ≤ Real.rpow L (1 / 100 : ℝ) := Real.one_le_rpow hL (by norm_num)
  have hM : (slotCount x : ℝ) ≤ 2 * Real.rpow L (1 / 100 : ℝ) := by
    simp only [slotCount, momentJ, Nat.cast_add, Nat.cast_one]
    have hfloor : (⌊Real.rpow (Real.log x) (1 / 100 : ℝ)⌋₊ : ℝ) ≤
        Real.rpow (Real.log x) (1 / 100 : ℝ) := Nat.floor_le (by positivity)
    have hLpowLog : 1 ≤ Real.rpow (Real.log x) (1 / 100 : ℝ) := by simpa [L] using hLpow
    calc
      (⌊Real.rpow (Real.log x) (1 / 100 : ℝ)⌋₊ : ℝ) + 1 ≤
          Real.rpow (Real.log x) (1 / 100 : ℝ) + Real.rpow (Real.log x) (1 / 100 : ℝ) :=
        add_le_add hfloor hLpowLog
      _ = 2 * Real.rpow L (1 / 100 : ℝ) := by simp [L]; ring
  have hlabel (i : Fin K) (j : Fin (slotCount x)) :
      (p i j : ℝ) ≤ Real.exp (2 * Real.rpow L (1 / 5 : ℝ)) := by
    rcases hp.1 i j with ⟨hprime, hmem⟩
    rcases Finset.mem_filter.mp hmem with ⟨_, ⟨_, _, hup⟩⟩
    have hai : a i ≤ 1 / 5 := (ha.2.1 i).2.le
    have hpow : Real.rpow L (a i) ≤ Real.rpow L (1 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL hai
    exact le_trans hup (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hpow (by norm_num)))
  have hprodBound :
      (∏ i : Fin K, ∏ j : Fin (slotCount x), (p i j : ℝ)) ≤
        ∏ i : Fin K, ∏ j : Fin (slotCount x), Real.exp (2 * Real.rpow L (1 / 5 : ℝ)) := by
    apply Finset.prod_le_prod₀
    · intro i hi
      exact Finset.prod_nonneg fun j hj => Nat.cast_nonneg _
    · intro i hi
      exact Finset.prod_le_prod₀ (fun j hj => Nat.cast_nonneg _) (fun j hj => hlabel i j)
  have hconst :
      (∏ i : Fin K, ∏ j : Fin (slotCount x), Real.exp (2 * Real.rpow L (1 / 5 : ℝ))) =
        Real.exp (2 * Real.rpow L (1 / 5 : ℝ) * ((K : ℝ) * slotCount x)) := by
    let E : ℝ := Real.exp (2 * Real.rpow L (1 / 5 : ℝ))
    calc
      (∏ i : Fin K, ∏ j : Fin (slotCount x), E) = (E ^ slotCount x) ^ K := by simp [E]
      _ = (Real.exp (2 * Real.rpow L (1 / 5 : ℝ) * (slotCount x : ℝ))) ^ K := by
        have hinner : E ^ slotCount x =
            Real.exp (2 * Real.rpow L (1 / 5 : ℝ) * (slotCount x : ℝ)) := by
          dsimp [E]
          calc
            Real.exp (2 * Real.rpow L (1 / 5 : ℝ)) ^ slotCount x =
                Real.exp ((slotCount x : ℝ) * (2 * Real.rpow L (1 / 5 : ℝ))) :=
                  (Real.exp_nat_mul (2 * Real.rpow L (1 / 5 : ℝ)) (slotCount x)).symm
            _ = Real.exp (2 * Real.rpow L (1 / 5 : ℝ) * (slotCount x : ℝ)) := by congr 1 <;> ring
        rw [hinner]
      _ = Real.exp ((K : ℝ) * (2 * Real.rpow L (1 / 5 : ℝ) * (slotCount x : ℝ))) :=
        (Real.exp_nat_mul (2 * Real.rpow L (1 / 5 : ℝ) * (slotCount x : ℝ)) K).symm
      _ = Real.exp (2 * Real.rpow L (1 / 5 : ℝ) * ((K : ℝ) * slotCount x)) := by
        congr 1 <;> ring
  have hpower : Real.rpow L (1 / 5 : ℝ) * Real.rpow L (1 / 100 : ℝ) =
      Real.rpow L (21 / 100 : ℝ) := by
    calc
      Real.rpow L (1 / 5 : ℝ) * Real.rpow L (1 / 100 : ℝ) =
          Real.rpow L ((1 / 5 : ℝ) + 1 / 100) := (Real.rpow_add hLpos _ _).symm
      _ = Real.rpow L (21 / 100 : ℝ) := by congr 1 <;> norm_num
  have hExp : 2 * Real.rpow L (1 / 5 : ℝ) * ((K : ℝ) * slotCount x) ≤
      4 * (K : ℝ) * Real.rpow L (21 / 100 : ℝ) := by
    have hKM : (K : ℝ) * slotCount x ≤ (K : ℝ) * (2 * Real.rpow L (1 / 100 : ℝ)) :=
      mul_le_mul_of_nonneg_left hM (Nat.cast_nonneg K)
    calc
      2 * Real.rpow L (1 / 5 : ℝ) * ((K : ℝ) * slotCount x) ≤
          2 * Real.rpow L (1 / 5 : ℝ) * ((K : ℝ) * (2 * Real.rpow L (1 / 100 : ℝ))) :=
            mul_le_mul_of_nonneg_left hKM (mul_nonneg (by norm_num)
              (Real.rpow_nonneg (le_of_lt hLpos) _))
      _ = 4 * (K : ℝ) * (Real.rpow L (1 / 5 : ℝ) * Real.rpow L (1 / 100 : ℝ)) := by ring
      _ = 4 * (K : ℝ) * Real.rpow L (21 / 100 : ℝ) := by rw [hpower]
  calc
    (∏ i : Fin K, ∏ j : Fin (slotCount x), (p i j : ℝ)) ≤
        Real.exp (2 * Real.rpow L (1 / 5 : ℝ) * ((K : ℝ) * slotCount x)) :=
          hprodBound.trans_eq hconst
    _ ≤ Real.exp (4 * (K : ℝ) * Real.rpow L (21 / 100 : ℝ)) :=
      Real.exp_le_exp.mpr hExp

/-- Every prime factor of a valid list product is one of its listed labels. -/
private theorem primeFactor_listProduct_mem {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (p : PrimeLists x K) (hp : ValidPrimeLists x K a p) (q : ℕ)
    (hq : q ∈ (∏ i : Fin K, ∏ j : Fin (slotCount x), p i j).primeFactors) :
    ∃ i j, q = p i j := by
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqDvd := Nat.dvd_of_mem_primeFactors hq
  have hqDvdProd : q ∣ ∏ ij : Fin K × Fin (slotCount x), p ij.1 ij.2 := by
    simpa [Fintype.prod_prod_type] using hqDvd
  rcases (hqPrime.prime.dvd_finsetProd_iff
      (fun ij : Fin K × Fin (slotCount x) => p ij.1 ij.2)).mp hqDvdProd with ⟨ij, _, hdiv⟩
  rcases (Nat.dvd_prime (hp.1 ij.1 ij.2).1).mp hdiv with hqone | hqeq
  · exact (hqPrime.ne_one hqone).elim
  · exact ⟨ij.1, ij.2, hqeq⟩

/-- The completion coordinate of a physical state is the canonical modular root residue. -/
private theorem physical_completionC_eq_rootC {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    {H' Hm Hn : ℝ} (P : PhysicalState x K a H' Hm Hn) (hfirst : 2 ≤ P.first) :
    P.completionC = (rootC P.first P.second : ℤ) := by
  letI : NeZero P.first := ⟨by omega⟩
  letI : Fact (1 < P.first) := ⟨by omega⟩
  have hdetMod := congrArg (fun z : ℤ => (z : ZMod P.first)) P.det_one
  have hdetMod' : -((P.second : ZMod P.first) * (P.completionC : ZMod P.first)) = 1 := by
    simpa using hdetMod
  have hmul : (P.second : ZMod P.first) * (P.completionC : ZMod P.first) = -1 := by
    have h := congrArg Neg.neg hdetMod'
    simpa using h
  have hv : IsUnit (P.second : ZMod P.first) :=
    (ZMod.isUnit_iff_coprime P.second P.first).2 P.primitive.symm
  have hunitInv : (↑(hv.unit⁻¹) : ZMod P.first) = (P.second : ZMod P.first)⁻¹ := by
    calc
      (↑(hv.unit⁻¹) : ZMod P.first) = (↑hv.unit : ZMod P.first)⁻¹ :=
        (ZMod.inv_coe_unit hv.unit).symm
      _ = (P.second : ZMod P.first)⁻¹ := by rw [hv.unit_spec]
  have hleft : (↑(hv.unit⁻¹) : ZMod P.first) * (P.second : ZMod P.first) = 1 := by
    simp [hv.unit_spec]
  have hcMod : (P.completionC : ZMod P.first) = -((P.second : ZMod P.first)⁻¹) := by
    calc
      (P.completionC : ZMod P.first) =
          1 * (P.completionC : ZMod P.first) := by simp
      _ = ((↑(hv.unit⁻¹) : ZMod P.first) * (P.second : ZMod P.first)) *
            (P.completionC : ZMod P.first) := by rw [hleft]
      _ = ↑(hv.unit⁻¹) *
            ((P.second : ZMod P.first) * (P.completionC : ZMod P.first)) := by ring
      _ = ↑(hv.unit⁻¹) * (-1) := by rw [hmul]
      _ = -((P.second : ZMod P.first)⁻¹) := by rw [hunitInv]; ring
  have hcast : (P.completionC : ZMod P.first) = (rootC P.first P.second : ZMod P.first) := by
    rw [hcMod]
    simp [rootC]
  have hcastInt : (P.completionC : ZMod P.first) =
      ((rootC P.first P.second : ℤ) : ZMod P.first) := by
    simpa using hcast
  have hmod : P.completionC % P.first = (rootC P.first P.second : ℤ) % P.first :=
    (ZMod.intCast_eq_intCast_iff' P.completionC (rootC P.first P.second : ℤ) P.first).mp hcastInt
  have hC := P.completion_range
  have hroot : (rootC P.first P.second : ℤ) < P.first := by
    exact_mod_cast (ZMod.val_lt (-((P.second : ZMod P.first)⁻¹)))
  rw [Int.emod_eq_of_lt hC.1 hC.2,
    Int.emod_eq_of_lt (Int.natCast_nonneg _) hroot] at hmod
  exact hmod

/-- A prime dividing the first coordinate has the vertical projective kernel line. -/
private theorem kernelLine_eq_last_of_dvd (p u c : ℕ) (hpu : p ∣ u) :
    kernelLine p u c = Fin.last p := by
  have huZero : (u : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff u p).2 hpu
  simp [kernelLine, projLine]
  intro hnot
  exact (hnot huZero).elim

/-- Every prime in a valid label product has the fixed vertical line when all labels divide `u`. -/
private theorem rootLines_last_of_list_divides {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (p : PrimeLists x K) (hp : ValidPrimeLists x K a p) (u v : ℕ)
    (hdiv : ∀ i j, p i j ∣ u) :
    ∀ q ∈ (∏ i : Fin K, ∏ j : Fin (slotCount x), p i j).primeFactors,
      kernelLine q u (rootC u v) = Fin.last q := by
  intro q hq
  obtain ⟨i, j, rfl⟩ := primeFactor_listProduct_mem p hp q hq
  exact kernelLine_eq_last_of_dvd _ _ _ (hdiv i j)

/-- At fixed positive scales, the physical-state space is finite. -/
private theorem physicalState_finite {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    {H' Hm Hn : ℝ} (hH' : 0 < H') (hHm : 0 < Hm) (hHn : 0 < Hn) :
    Set.Finite (Set.univ : Set (PhysicalState x K a H' Hm Hn)) := by
  classical
  let N₁ : ℕ := ⌊16 * H' * Hm⌋₊
  let N₂ : ℕ := ⌊2 * Hn⌋₊
  let LabelCode := (i : Fin K) → (j : Fin (slotCount x)) →
    {q : ℕ // q ∈ primeBand x (a i)}
  let Code := (Fin (N₁ + 1) × Fin (N₂ + 1)) × LabelCode
  letI (i : Fin K) : Fintype {q : ℕ // q ∈ primeBand x (a i)} :=
    Fintype.ofFinset (primeBand x (a i)) (by intro q; rfl)
  let code (P : PhysicalState x K a H' Hm Hn) : Code :=
    ((⟨P.first, by
        have hreal : (P.first : ℝ) ≤ 16 * H' * Hm := P.first_upper
        exact Nat.lt_succ_of_le ((Nat.le_floor_iff (by positivity)).2 hreal)⟩,
      ⟨P.second, by
        have hreal : (P.second : ℝ) ≤ 2 * Hn := P.second_upper
        exact Nat.lt_succ_of_le ((Nat.le_floor_iff (by positivity)).2 hreal)⟩),
      fun i j => ⟨P.labels i j, P.label_in_band i j⟩)
  have hfirstpos (P : PhysicalState x K a H' Hm Hn) : 0 < P.first := by
    by_contra hnot
    have hzero : P.first = 0 := by omega
    have hle : H' * Hm ≤ 0 := by simpa [hzero] using P.first_lower
    exact (not_le_of_gt (mul_pos hH' hHm)) hle
  have hinj : Function.Injective code := by
    intro P Q hPQ
    have hfirst : P.first = Q.first := congrArg (fun z : Code => z.1.1.val) hPQ
    have hsecond : P.second = Q.second := congrArg (fun z : Code => z.1.2.val) hPQ
    have hlabels : ∀ i j, P.labels i j = Q.labels i j := by
      intro i j
      have hlabel := congrArg (fun z : Code => z.2 i j) hPQ
      exact congrArg Subtype.val hlabel
    have hlabelsFun : P.labels = Q.labels := by
      funext i
      funext j
      exact hlabels i j
    have hcompletionC : P.completionC = Q.completionC := by
      by_cases hbig : 2 ≤ P.first
      · have hP := physical_completionC_eq_rootC P hbig
        have hQ := physical_completionC_eq_rootC Q (by omega)
        rw [hP, hQ, hfirst, hsecond]
      · have hone : P.first = 1 := by
          have := hfirstpos P
          omega
        have hQone : Q.first = 1 := by omega
        have hPzero : P.completionC = 0 := by
          rcases P.completion_range with ⟨hlo, hhi⟩
          rw [hone] at hhi
          omega
        have hQzero : Q.completionC = 0 := by
          rcases Q.completion_range with ⟨hlo, hhi⟩
          rw [hQone] at hhi
          omega
        rw [hPzero, hQzero]
    have hcompletionD : P.completionD = Q.completionD := by
      have hQdet : (P.first : ℤ) * Q.completionD -
          (P.second : ℤ) * P.completionC = 1 := by
        simpa [hfirst, hsecond, hcompletionC] using Q.det_one
      have hmul : (P.first : ℤ) * (P.completionD - Q.completionD) = 0 := by
        rw [Int.mul_sub]
        nlinarith [P.det_one, hQdet]
      rcases mul_eq_zero.mp hmul with hzero | hzero
      · have hfirstInt : (P.first : ℤ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt (hfirstpos P))
        exact (hfirstInt hzero).elim
      · exact sub_eq_zero.mp hzero
    cases P
    cases Q
    simp_all [PhysicalState.mk.injEq]
  letI : Fintype LabelCode := inferInstance
  letI : Fintype Code := inferInstance
  letI : Finite (PhysicalState x K a H' Hm Hn) := Finite.of_injective code hinj
  exact Set.toFinite _

/-- With a finite physical-state instance, the pairing's outer counting sum is finite. -/
private theorem detPairing_outer_finite_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    [Fintype (PState F S)] :
    detPairing F S family beta =
      (physicalMeasure S.x K F.a : ℂ) *
        ∑ P : PState F S,
          endpointF S.x K F.a family beta P *
            detOp F S (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta) P := by
  unfold detPairing
  rw [tsum_fintype]

/-- The no-good pairing's outer counting sum is finite under the same state instance. -/
private theorem detPairingNoGood_outer_finite_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    [Fintype (PState F S)] :
    detPairingNoGood F S family beta =
      (physicalMeasure S.x K F.a : ℂ) *
        ∑ P : PState F S,
          endpointF S.x K F.a family beta P *
            physSym F S (physRow F S (physSym F S
              (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta))) P := by
  unfold detPairingNoGood
  rw [tsum_fintype]

/-- The physical row action is a finite sum whenever the state space has a Fintype instance. -/
private theorem physRow_finite_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    [Fintype (PState F S)] (f : PState F S → ℂ) (P : PState F S) :
    physRow F S f P = ∑ Q : PState F S, physRowKernel F S P Q * f Q := by
  unfold physRow
  rw [tsum_fintype]

/-- The no-good pairing as a finite sum over its source and target physical states. -/
private theorem detPairingNoGood_finiteDoubleSum {K : ℕ} (F : PDFix K) (S : PDScale)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    [Fintype (PState F S)] :
    detPairingNoGood F S family beta =
      (physicalMeasure S.x K F.a : ℂ) *
        ∑ P : PState F S,
          endpointF S.x K F.a family beta P *
            physSym F S (fun R : PState F S =>
              ∑ Q : PState F S, physRowKernel F S R Q *
                physSym F S (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta) Q) P := by
  classical
  rw [detPairingNoGood_outer_finite_sum]
  have hrow :
      physRow F S (physSym F S
        (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta)) =
      (fun R : PState F S =>
        ∑ Q : PState F S, physRowKernel F S R Q *
          physSym F S
            (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta) Q) := by
    funext R
    exact physRow_finite_sum F S _ R
  rw [hrow]

/-- The good pairing as a finite sum, retaining both goodness projections. -/
private theorem detPairing_finiteDoubleSum {K : ℕ} (F : PDFix K) (S : PDScale)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    [Fintype (PState F S)] :
    detPairing F S family beta =
      (physicalMeasure S.x K F.a : ℂ) *
        ∑ P : PState F S,
          endpointF S.x K F.a family beta P *
            physGood F S
              (physSym F S (fun R : PState F S =>
                ∑ Q : PState F S, physRowKernel F S R Q *
                  physSym F S (physGood F S
                    (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta)) Q)) P := by
  classical
  rw [detPairing_outer_finite_sum]
  unfold detOp
  have hrow :
      physRow F S (physSym F S (physGood F S
        (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta))) =
      (fun R : PState F S =>
        ∑ Q : PState F S, physRowKernel F S R Q *
          physSym F S (physGood F S
            (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta)) Q) := by
    funext R
    exact physRow_finite_sum F S _ R
  rw [hrow]

/-- `t2:pd.goodness-removal` (new node, part of `t2:pd.strip-goodness-pads`) — PD 04:970-1008.
Removing both good-state projections from the pairing costs `O_A(UV L^{-A})`: majorize the bad
parts absolutely with log-power endpoint suprema; single-edge root replacement (the general
sub-lemmas `root_lines`, `root_arch_boundary`, `root_bonferroni`); one-edge label mass
(mem:one-edge-label-mass) `≤ 1`; `O(1)` raw / `O(Y)` comparison targets; bad ratios of measure
`e^{-cL^{0.1}}` by `good_state`. -/
theorem goodness_removal (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ family : CoefficientFamily δ C c₁ c₂, FamilyAtScale family S →
          family.xMin ≤ S.x →
          ∀ beta : ℕ → ℂ, IsSecondCoefficient S C beta →
            ‖detPairing F S family beta - detPairingNoGood F S family beta‖ ≤
              C_A * S.U * S.V * Real.rpow S.L (-A) := by
  sorry

/-- `t2:pd.pad-stripping` (new node, part of `t2:pd.strip-goodness-pads`) — PD 04:1010-1101.
Summed over pad dyads with weight `1/d₀`, the pairing without goodness is the coprime Cauchy
square minus the unrestricted major sum up to `O_A(XY L^{-A})`: pad measure identity
(mem:pad-measure) (pads are independent ordered harmonic draws, total mass one), raw part =
coprime pairs `(a,b)` (the cross-edge ban), pad collisions (mem:pad-collisions) against the
absolute squares (mem:raw-absolute-square), (mem:comparison-absolute-square), and restoration of
non-disjoint `(a,b)` in the comparison (mem:unshared-collisions). -/
theorem pad_stripping (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
        ∀ family : CoefficientFamily δ C c₁ c₂, family.xMin ≤ x → ∀ beta : ℕ → ℂ,
          IsFamilySecondCoefficient family x beta → ∀ Y ∈ dyadicScales x K,
            ‖(∑ d₀ ∈ padScales x K,
                ((d₀ : ℂ))⁻¹ * detPairingNoGood F (familyScale family x Y d₀) family beta) -
                ((coprimeCauchySquare x K F.a Y family beta F.eta : ℂ) -
                  majorArcSum x K F.a Y F.A₀ family beta F.eta F.psi)‖ ≤
              C_A * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A) := by
  sorry

/-- `t2:pd.strip-goodness-pads` — PD 04:968-1117.  REPLACES the frozen `strip_goodness_pads`
(which asserted the replacement for every `K` and `A₀` without the pairing hypothesis).  From
pairing bounds at every pad dyad to the replacement of the Cauchy square: `goodness_removal`,
`pad_stripping`, and part (iii) of the frozen `cauchy_decomposition` (`Q_Y` vs `Q_Y^{cop}`);
`UV/d₀ = XY`. -/
theorem strip_goodness_pads (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
        ∀ family : CoefficientFamily δ C c₁ c₂, family.xMin ≤ x → ∀ beta : ℕ → ℂ,
          IsFamilySecondCoefficient family x beta → ∀ Y ∈ dyadicScales x K,
            ∀ E₀ Ce Cp : ℝ,
              (∀ d₀ ∈ padScales x K,
                ‖detPairing F (familyScale family x Y d₀) family beta‖ ≤
                  Cp * (familyScale family x Y d₀).U * (familyScale family x Y d₀).V *
                    Real.rpow (Real.log x) (-E₀ + Ce)) →
              ‖(cauchySquare x K F.a Y family beta F.eta : ℂ) -
                  majorArcSum x K F.a Y F.A₀ family beta F.eta F.psi‖ ≤
                ((padScales x K).card : ℝ) * Cp * (family.Hm x * family.Hn x) * Y *
                    Real.rpow (Real.log x) (-E₀ + Ce) +
                C_A * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A) := by
  intro K F hF A hA
  by_cases hc₂ : 0 < c₂
  · let hFKeep : F.Valid := hF
    rcases hF with ⟨hBands, hqd₀, hqd₁, hA₀, hEtaCut, hPsiCut⟩
    rcases hEtaCut with ⟨hEtaSmooth, hEtaSupport, hEtaNonneg, hEtaPartition⟩
    rcases hPsiCut with ⟨hPsiSmooth, hPsiCompact, hPsiOne⟩
    let Aerr : ℝ := A + 1
    have hAerr : 0 < Aerr := by dsimp [Aerr]; linarith
    obtain ⟨Cgood, xGood, hCgood, hxGood₂, goodnessRemoval⟩ :=
      goodness_removal δ C c₁ c₂ hδ hC hc₁ K F hFKeep Aerr hAerr
    obtain ⟨Cpad, xPad, hCpad, hxPad₂, padStripping⟩ :=
      pad_stripping δ C c₁ c₂ hδ hC hc₁ K F hFKeep A hA
    obtain ⟨Cdec, Cscale, Cmain, CDiv, xDec, hCdec, hCscale, hCmain, hCDiv, hxDec₂,
      cauchyDecomposition⟩ :=
      cauchy_decomposition δ C (1 : ℝ) F.q_d c₁ c₂ K F.a hδ hC (by norm_num)
        hqd₀ hqd₁ hc₁ hc₂ hBands A hA
    let Ccard : ℝ := ((K + 1 : ℕ) : ℝ) + 1
    let C_A : ℝ := Ccard * Cgood + Cpad + Cdec
    let x₀ : ℝ := max xGood (max xPad (max xDec (Real.exp 1)))
    have hC_A : 0 < C_A := by
      dsimp [C_A]
      positivity
    have hx₀Good : xGood ≤ x₀ := by simp [x₀]
    have hx₀Pad : xPad ≤ x₀ := by simp [x₀]
    have hx₀Dec : xDec ≤ x₀ := by simp [x₀]
    have hx₀Exp : Real.exp 1 ≤ x₀ := by simp [x₀]
    refine Exists.intro C_A ?_
    refine Exists.intro x₀ ?_
    constructor
    · exact hC_A
    constructor
    · exact le_trans hxGood₂ hx₀Good
    · intro x hx₀x family hfamilyMin beta hbeta Y hY E₀ Ce Cp hPairs
      have hxGood : xGood ≤ x := le_trans hx₀Good hx₀x
      have hxPad : xPad ≤ x := le_trans hx₀Pad hx₀x
      have hxDec : xDec ≤ x := le_trans hx₀Dec hx₀x
      have hx₂ : 2 ≤ x := le_trans hxGood₂ hxGood
      have hxExp : Real.exp 1 ≤ x := le_trans hx₀Exp hx₀x
      have hlog : 1 ≤ Real.log x := by
        have h := Real.log_le_log (Real.exp_pos 1) hxExp
        simpa using h
      have hlogpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hlog
      have hpowCard : Real.rpow (Real.log x) (21 / 100 : ℝ) ≤ Real.log x := by
        calc
          Real.rpow (Real.log x) (21 / 100 : ℝ) ≤ Real.rpow (Real.log x) 1 :=
            Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
          _ = Real.log x := by simp
      let u : ℝ := ((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ)
      have huEq : u = ((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ) := rfl
      have hu : 0 ≤ u := by dsimp [u]; positivity
      have hfloor : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu
      have hcardNat : (padScales x K).card ≤ ⌊u⌋₊ + 1 := by
        unfold padScales
        rw [← huEq]
        calc
          ((Finset.range (⌊u⌋₊ + 1)).image (fun k => 2 ^ k)).card ≤
              (Finset.range (⌊u⌋₊ + 1)).card := Finset.card_image_le
          _ = ⌊u⌋₊ + 1 := by simp
      have hcard : ((padScales x K).card : ℝ) ≤ Ccard * Real.log x := by
        calc
          ((padScales x K).card : ℝ) ≤ (⌊u⌋₊ : ℝ) + 1 := by exact_mod_cast hcardNat
          _ ≤ u + 1 := add_le_add hfloor le_rfl
          _ ≤ Ccard * Real.log x := by
            dsimp [u, Ccard]
            calc
              ((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ) + 1 ≤
                  ((K + 1 : ℕ) : ℝ) * Real.log x + Real.log x := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hpowCard (by positivity)) hlog
              _ = (((K + 1 : ℕ) : ℝ) + 1) * Real.log x := by ring
      have hHmLo : Real.rpow x δ ≤ family.Hm x := (family.scales x hfamilyMin).1
      have hHnLo : Real.rpow x δ ≤ family.Hn x := (family.scales x hfamilyMin).2.1
      have hxpos : 0 < x := by linarith
      have hpX : 0 < Real.rpow x δ := Real.rpow_pos_of_pos hxpos δ
      have hHmPos : 0 < family.Hm x := lt_of_lt_of_le hpX hHmLo
      have hHnPos : 0 < family.Hn x := lt_of_lt_of_le hpX hHnLo
      have hXYpos : 0 < family.Hm x * family.Hn x := mul_pos hHmPos hHnPos
      have hYpos : 0 < Y := by
        unfold dyadicScales at hY
        rcases Finset.mem_filter.mp hY with ⟨hImage, _⟩
        rcases Finset.mem_image.mp hImage with ⟨k, _, hYeq⟩
        calc
          0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
          _ = Y := hYeq
      have hScaleValid (d₀ : ℕ) (hd₀ : d₀ ∈ padScales x K) :
          (familyScale family x Y d₀).Valid K δ c₁ c₂ := by
        rcases family.scales x hfamilyMin with ⟨hHm, hHn, hprodLo, hprodHi⟩
        dsimp [PDScale.Valid, familyScale]
        exact ⟨hx₂, hHm, hHn, hprodLo, hprodHi, hY, hd₀⟩
      have hFamilyAt (d₀ : ℕ) : FamilyAtScale family (familyScale family x Y d₀) := by
        constructor <;> rfl
      have hBetaAt (d₀ : ℕ) : IsSecondCoefficient (familyScale family x Y d₀) C beta := by
        simpa [IsSecondCoefficient, IsFamilySecondCoefficient, familyScale] using hbeta
      have hD₀Pos (d₀ : ℕ) (hd₀ : d₀ ∈ padScales x K) : 0 < (d₀ : ℝ) := by
        unfold padScales at hd₀
        rcases Finset.mem_image.mp hd₀ with ⟨k, _, hEq⟩
        have hNat : 0 < d₀ := by
          calc
            0 < 2 ^ k := pow_pos (by norm_num : 0 < (2 : ℕ)) k
            _ = d₀ := hEq
        exact_mod_cast hNat
      have hGoodPair : ∀ d₀ ∈ padScales x K,
          ‖detPairing F (familyScale family x Y d₀) family beta -
            detPairingNoGood F (familyScale family x Y d₀) family beta‖ ≤
            Cgood * (familyScale family x Y d₀).U * (familyScale family x Y d₀).V *
              Real.rpow (Real.log x) (-Aerr) := by
        intro d₀ hd₀
        have hGoodAt := goodnessRemoval (familyScale family x Y d₀)
          (hScaleValid d₀ hd₀) (le_trans hx₀Good hx₀x) family (hFamilyAt d₀)
          hfamilyMin beta (hBetaAt d₀)
        simpa [familyScale, PDScale.L] using hGoodAt
      have hPairTerm (d₀ : ℕ) (hd₀ : d₀ ∈ padScales x K) :
          ‖((d₀ : ℂ))⁻¹ * detPairing F (familyScale family x Y d₀) family beta‖ ≤
            Cp * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-E₀ + Ce) := by
        have hInv : ‖((d₀ : ℂ))⁻¹‖ = (d₀ : ℝ)⁻¹ := by simp
        have hPairAt := hPairs d₀ hd₀
        calc
          ‖((d₀ : ℂ))⁻¹ * detPairing F (familyScale family x Y d₀) family beta‖ =
              (d₀ : ℝ)⁻¹ * ‖detPairing F (familyScale family x Y d₀) family beta‖ := by
                rw [norm_mul, hInv]
          _ ≤ (d₀ : ℝ)⁻¹ *
              (Cp * (familyScale family x Y d₀).U *
                (familyScale family x Y d₀).V * Real.rpow (Real.log x) (-E₀ + Ce)) :=
                mul_le_mul_of_nonneg_left hPairAt (by positivity)
          _ = Cp * (family.Hm x * family.Hn x) * Y *
                Real.rpow (Real.log x) (-E₀ + Ce) := by
                simp [familyScale, PDScale.U, PDScale.H, PDScale.V, PDScale.L]
                field_simp [ne_of_gt (hD₀Pos d₀ hd₀)]
      let GoodSum : ℂ := ∑ d₀ ∈ padScales x K,
        ((d₀ : ℂ))⁻¹ * detPairing F (familyScale family x Y d₀) family beta
      let NoGoodSum : ℂ := ∑ d₀ ∈ padScales x K,
        ((d₀ : ℂ))⁻¹ * detPairingNoGood F (familyScale family x Y d₀) family beta
      have hGoodSum : ‖GoodSum‖ ≤ ((padScales x K).card : ℝ) * Cp *
          (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-E₀ + Ce) := by
        dsimp [GoodSum]
        calc
          ‖∑ d₀ ∈ padScales x K,
              ((d₀ : ℂ))⁻¹ * detPairing F (familyScale family x Y d₀) family beta‖ ≤
            ∑ d₀ ∈ padScales x K,
              ‖((d₀ : ℂ))⁻¹ * detPairing F (familyScale family x Y d₀) family beta‖ :=
                norm_sum_le _ _
          _ ≤ ∑ d₀ ∈ padScales x K,
              Cp * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-E₀ + Ce) :=
                Finset.sum_le_sum fun d₀ hd₀ => hPairTerm d₀ hd₀
          _ = ((padScales x K).card : ℝ) * Cp *
              (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-E₀ + Ce) := by
                simp [mul_assoc]
      have hGoodErrorTerm (d₀ : ℕ) (hd₀ : d₀ ∈ padScales x K) :
          ‖((d₀ : ℂ))⁻¹ *
              (detPairing F (familyScale family x Y d₀) family beta -
                detPairingNoGood F (familyScale family x Y d₀) family beta)‖ ≤
            Cgood * (family.Hm x * family.Hn x) * Y *
              Real.rpow (Real.log x) (-A - 1) := by
        have hInv : ‖((d₀ : ℂ))⁻¹‖ = (d₀ : ℝ)⁻¹ := by simp
        have hGoodAt := hGoodPair d₀ hd₀
        have hExpErr : -Aerr = -A - 1 := by dsimp [Aerr]; ring
        rw [hExpErr] at hGoodAt
        calc
          ‖((d₀ : ℂ))⁻¹ *
              (detPairing F (familyScale family x Y d₀) family beta -
                detPairingNoGood F (familyScale family x Y d₀) family beta)‖ =
              (d₀ : ℝ)⁻¹ *
                ‖detPairing F (familyScale family x Y d₀) family beta -
                  detPairingNoGood F (familyScale family x Y d₀) family beta‖ := by
                    rw [norm_mul, hInv]
          _ ≤ (d₀ : ℝ)⁻¹ * (Cgood * (familyScale family x Y d₀).U *
                (familyScale family x Y d₀).V * Real.rpow (Real.log x) (-A - 1)) :=
                  mul_le_mul_of_nonneg_left hGoodAt (by positivity)
          _ = Cgood * (family.Hm x * family.Hn x) * Y *
                Real.rpow (Real.log x) (-A - 1) := by
                  simp [familyScale, PDScale.U, PDScale.H, PDScale.V, PDScale.L]
                  field_simp [ne_of_gt (hD₀Pos d₀ hd₀)]
      have hGoodError : ‖GoodSum - NoGoodSum‖ ≤
          ((padScales x K).card : ℝ) * Cgood * (family.Hm x * family.Hn x) * Y *
            Real.rpow (Real.log x) (-A - 1) := by
        have hSumEq : GoodSum - NoGoodSum =
            ∑ d₀ ∈ padScales x K,
              ((d₀ : ℂ))⁻¹ *
                (detPairing F (familyScale family x Y d₀) family beta -
                  detPairingNoGood F (familyScale family x Y d₀) family beta) := by
          dsimp [GoodSum, NoGoodSum]
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro d₀ hd₀
          ring
        rw [hSumEq]
        calc
          ‖∑ d₀ ∈ padScales x K,
              ((d₀ : ℂ))⁻¹ *
                (detPairing F (familyScale family x Y d₀) family beta -
                  detPairingNoGood F (familyScale family x Y d₀) family beta)‖ ≤
            ∑ d₀ ∈ padScales x K,
              ‖((d₀ : ℂ))⁻¹ *
                (detPairing F (familyScale family x Y d₀) family beta -
                  detPairingNoGood F (familyScale family x Y d₀) family beta)‖ :=
                norm_sum_le _ _
          _ ≤ ∑ d₀ ∈ padScales x K,
              Cgood * (family.Hm x * family.Hn x) * Y *
                Real.rpow (Real.log x) (-A - 1) :=
                Finset.sum_le_sum fun d₀ hd₀ => hGoodErrorTerm d₀ hd₀
          _ = ((padScales x K).card : ℝ) * Cgood *
              (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A - 1) := by
                simp [mul_assoc]
      have hpowErr : Real.log x * Real.rpow (Real.log x) (-A - 1) =
          Real.rpow (Real.log x) (-A) := by
        calc
          Real.log x * Real.rpow (Real.log x) (-A - 1) =
              Real.rpow (Real.log x) (-A - 1) * Real.log x := by ring
          _ = Real.rpow (Real.log x) ((-A - 1) + 1) :=
            (Real.rpow_add_one (ne_of_gt hlogpos) (-A - 1)).symm
          _ = Real.rpow (Real.log x) (-A) := by congr 1 <;> ring
      have hErrFactor : 0 ≤ Cgood * (family.Hm x * family.Hn x) * Y *
          Real.rpow (Real.log x) (-A - 1) := by
        exact le_of_lt (mul_pos (mul_pos (mul_pos hCgood hXYpos) hYpos)
          (Real.rpow_pos_of_pos hlogpos _))
      have hGoodErrorSaved : ‖GoodSum - NoGoodSum‖ ≤
          Ccard * Cgood * (family.Hm x * family.Hn x) * Y *
            Real.rpow (Real.log x) (-A) := by
        calc
          ‖GoodSum - NoGoodSum‖ ≤
              ((padScales x K).card : ℝ) * Cgood *
                (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A - 1) :=
            hGoodError
          _ = ((padScales x K).card : ℝ) *
                (Cgood * (family.Hm x * family.Hn x) * Y *
                  Real.rpow (Real.log x) (-A - 1)) := by ring
          _ ≤ (Ccard * Real.log x) *
                (Cgood * (family.Hm x * family.Hn x) * Y *
                  Real.rpow (Real.log x) (-A - 1)) :=
                mul_le_mul_of_nonneg_right hcard hErrFactor
          _ = Ccard * Cgood * (family.Hm x * family.Hn x) * Y *
                (Real.log x * Real.rpow (Real.log x) (-A - 1)) := by ring
          _ = Ccard * Cgood * (family.Hm x * family.Hn x) * Y *
                Real.rpow (Real.log x) (-A) := by rw [hpowErr]
      let alphaAtX : ℝ → ℕ → ℂ := fun y m => if y = x then family.alpha x m else 0
      let familyAtX : CoefficientFamily δ C c₁ c₂ :=
        { xMin := family.xMin
          xMin_ge_two := family.xMin_ge_two
          Hm := family.Hm
          Hn := family.Hn
          interval := family.interval
          alpha := alphaAtX
          interval_property := family.interval_property
          scales := family.scales
          interval_bounds := family.interval_bounds
          rough_support := by
            intro y hy m hne
            by_cases hxy : y = x
            · subst y
              have hα : family.alpha x m ≠ 0 := by simpa [alphaAtX] using hne
              simpa [alphaAtX] using family.rough_support x hy m hα
            · have hzero : alphaAtX y m = 0 := by simp [alphaAtX, hxy]
              exact (hne hzero).elim
          coefficient_bound := by
            intro y hy m hm
            by_cases hxy : y = x
            · subst y
              simpa [alphaAtX] using family.coefficient_bound x hy m hm
            · have hy₂ : 2 ≤ y := le_trans family.xMin_ge_two hy
              have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
              simp [alphaAtX, hxy]
              exact (Real.rpow_pos_of_pos hlogy C).le }
      have hLong : HasLongCoefficientCancellation familyAtX := by
        intro A₀ B A hA₀ hB hA
        refine Exists.intro (1 : ℝ) ?_
        refine Exists.intro (max 2 (x + 1)) ?_
        constructor
        · norm_num
        constructor
        · exact le_max_left _ _
        constructor
        · have hxto : x ≤ max 2 (x + 1) := by
            exact le_trans (by linarith : x ≤ x + 1) (le_max_right _ _)
          simpa [familyAtX] using le_trans hfamilyMin hxto
        · intro y hy k hk₁ hk₂ χ t ht
          have hxPlus : x + 1 ≤ y := le_trans (le_max_right _ _) hy
          have hxy : x < y := by linarith
          have hy₂ : 2 ≤ y := le_trans (le_max_left _ _) hy
          have hlogy : 0 < Real.log y := Real.log_pos (by linarith)
          simpa [familyTerms, familyAtX, alphaAtX, ne_of_gt hxy] using
            (Real.rpow_pos_of_pos hlogy (-A)).le
      have hBetaParts := hbeta
      rcases hBetaParts with ⟨hBetaSupport, hBetaBound⟩
      have hBetaSupportX : ∀ n, beta n ≠ 0 →
          n ∈ dyadicIntegers (familyAtX.Hn x) ∧ roughAbove n (roughCutoff x) := by
        simpa [familyAtX] using hBetaSupport
      have hBetaBoundX : ∀ n ∈ dyadicIntegers (familyAtX.Hn x),
          ‖beta n‖ ≤ Real.rpow (Real.log x) C := by
        simpa [familyAtX] using hBetaBound
      have hOneInvariant : IsMarkedInvariant x K F.a (fun _ : ℕ => (1 : ℂ)) := by
        constructor
        · intro n
          simp
        · intro p n hp hprime
          rfl
      have hDecAt := cauchyDecomposition familyAtX hLong x (le_trans hx₀Dec hx₀x) hfamilyMin
        F.eta hEtaSmooth hEtaSupport hEtaNonneg hEtaPartition beta
          hBetaSupportX hBetaBoundX (fun _ : ℕ => (1 : ℂ)) hOneInvariant
      have hCollX := (hDecAt.2.1 Y hY).2.2
      have hTerms : familyTerms familyAtX x = familyTerms family x := by
        simp [familyTerms, familyAtX]
      have hAlpha : familyAtX.alpha x = family.alpha x := by
        funext m
        simp [familyAtX, alphaAtX]
      have hCauchyEq :
          cauchySquare x K F.a Y familyAtX beta F.eta =
            cauchySquare x K F.a Y family beta F.eta := by
        simp [cauchySquare, hTerms, hAlpha, familyAtX, alphaAtX]
      have hCoprimeEq :
          coprimeCauchySquare x K F.a Y familyAtX beta F.eta =
            coprimeCauchySquare x K F.a Y family beta F.eta := by
        simp [coprimeCauchySquare, hTerms, hAlpha, familyAtX, alphaAtX]
      have hColl :
          |cauchySquare x K F.a Y family beta F.eta -
            coprimeCauchySquare x K F.a Y family beta F.eta| ≤
          Cdec * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A) := by
        simpa [hCauchyEq, hCoprimeEq, familyAtX] using hCollX
      have hPadDirect := padStripping x hxPad family hfamilyMin beta hbeta Y hY
      let B : ℂ := (coprimeCauchySquare x K F.a Y family beta F.eta : ℂ) -
        majorArcSum x K F.a Y F.A₀ family beta F.eta F.psi
      have hPadErr : ‖NoGoodSum - B‖ ≤
          Cpad * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A) := by
        simpa [NoGoodSum, B] using hPadDirect
      let Ccol : ℂ :=
        ((cauchySquare x K F.a Y family beta F.eta -
          coprimeCauchySquare x K F.a Y family beta F.eta : ℝ) : ℂ)
      have hCollNorm : ‖Ccol‖ ≤
          Cdec * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A) := by
        change ‖((cauchySquare x K F.a Y family beta F.eta -
          coprimeCauchySquare x K F.a Y family beta F.eta : ℝ) : ℂ)‖ ≤ _
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact hColl
      have hDecomp :
          (cauchySquare x K F.a Y family beta F.eta : ℂ) -
              majorArcSum x K F.a Y F.A₀ family beta F.eta F.psi =
            (GoodSum + (NoGoodSum - GoodSum)) + ((B - NoGoodSum) + Ccol) := by
        have hBase : (cauchySquare x K F.a Y family beta F.eta : ℂ) -
            majorArcSum x K F.a Y F.A₀ family beta F.eta F.psi = B + Ccol := by
          dsimp [B, Ccol]
          push_cast
          ring
        rw [hBase]
        ring
      have hGoodErrorRev : ‖NoGoodSum - GoodSum‖ ≤
          Ccard * Cgood * (family.Hm x * family.Hn x) * Y *
            Real.rpow (Real.log x) (-A) := by
        calc
          ‖NoGoodSum - GoodSum‖ = ‖GoodSum - NoGoodSum‖ := by rw [norm_sub_rev]
          _ ≤ Ccard * Cgood * (family.Hm x * family.Hn x) * Y *
                Real.rpow (Real.log x) (-A) := hGoodErrorSaved
      have hPadErrorRev : ‖B - NoGoodSum‖ ≤
          Cpad * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A) := by
        calc
          ‖B - NoGoodSum‖ = ‖NoGoodSum - B‖ := by rw [norm_sub_rev]
          _ ≤ Cpad * (family.Hm x * family.Hn x) * Y *
                Real.rpow (Real.log x) (-A) := hPadErr
      have hErrSum :
          ‖NoGoodSum - GoodSum‖ + ‖B - NoGoodSum‖ + ‖Ccol‖ ≤
            C_A * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A) := by
        calc
          _ ≤ Ccard * Cgood * (family.Hm x * family.Hn x) * Y *
                Real.rpow (Real.log x) (-A) +
              Cpad * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A) +
              Cdec * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A) :=
                add_le_add (add_le_add hGoodErrorRev hPadErrorRev) hCollNorm
          _ = C_A * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A) := by
                dsimp [C_A]
                ring
      have hTriangle :
          ‖(cauchySquare x K F.a Y family beta F.eta : ℂ) -
              majorArcSum x K F.a Y F.A₀ family beta F.eta F.psi‖ ≤
            ‖GoodSum‖ + ‖NoGoodSum - GoodSum‖ + ‖B - NoGoodSum‖ + ‖Ccol‖ := by
        rw [hDecomp]
        calc
          ‖(GoodSum + (NoGoodSum - GoodSum)) + ((B - NoGoodSum) + Ccol)‖ ≤
              ‖GoodSum + (NoGoodSum - GoodSum)‖ + ‖(B - NoGoodSum) + Ccol‖ :=
                norm_add_le _ _
          _ ≤ (‖GoodSum‖ + ‖NoGoodSum - GoodSum‖) +
              (‖B - NoGoodSum‖ + ‖Ccol‖) :=
                add_le_add (norm_add_le _ _) (norm_add_le _ _)
          _ = ‖GoodSum‖ + ‖NoGoodSum - GoodSum‖ +
                ‖B - NoGoodSum‖ + ‖Ccol‖ := by ring
      calc
        ‖(cauchySquare x K F.a Y family beta F.eta : ℂ) -
            majorArcSum x K F.a Y F.A₀ family beta F.eta F.psi‖ ≤
          ‖GoodSum‖ + ‖NoGoodSum - GoodSum‖ + ‖B - NoGoodSum‖ + ‖Ccol‖ := hTriangle
        _ ≤ ((padScales x K).card : ℝ) * Cp * (family.Hm x * family.Hn x) * Y *
              Real.rpow (Real.log x) (-E₀ + Ce) +
            C_A * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A) := by
              simpa [add_assoc] using add_le_add hGoodSum hErrSum
  · sorry

set_option maxHeartbeats 1000000
/-- `prop:minor-moment` (moment part) — PD 04:11-22, Proposition 4.1.  REPLACES the first
conjunct of the frozen `minor_moment`.  For every `E₀` choose `A₀`, then `K₀` (independent of the
band exponents): the determinant moment is `≤ L^{-E₀N}`.  Proof: `path_expansion`,
`root_replacement` (`A = E₀+1`), `memory_identity`, `truncation_adjoint`, `birth_distinctness`
with `ρ = q_d^{1/8}`, `0 ≤ b'_p ≤ 1`, root region of volume `15`. -/
theorem minor_moment (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) (q_d : ℝ) (eta psi : ℝ → ℝ) :
    ∀ E₀ : ℝ, 0 < E₀ → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ,
      ∀ (K : ℕ), K₀ ≤ K → ∀ (F : PDFix K), F.Valid → F.Has q_d A₀ eta psi →
        ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
          detMoment F S ≤ Real.rpow S.L (-E₀ * (S.N : ℝ)) := by
  intro E₀ hE₀
  obtain ⟨A₀, hA₀, K₀, birthDistinctness⟩ :=
    birth_distinctness δ c₁ c₂ hδ hc₁ q_d eta psi E₀ hE₀
  refine ⟨A₀, hA₀, K₀, ?_⟩
  intro K hK F hF hHas
  have hBands : ValidBands K F.a := hF.1
  have hqd₀ : 0 < F.q_d := hF.2.1
  have hqd₁ : F.q_d < 1 := hF.2.2.1
  let ρ : ℝ := (1 + Real.sqrt F.q_d) / 2
  have hsqrt₀ : 0 < Real.sqrt F.q_d := Real.sqrt_pos.2 hqd₀
  have hsqrt₁ : Real.sqrt F.q_d < 1 :=
    (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2 (by nlinarith)
  have hρ : IsMemoryRho F.q_d ρ := by
    unfold IsMemoryRho ρ
    constructor
    · positivity
    constructor
    · nlinarith
    · nlinarith [sq_nonneg (1 - Real.sqrt F.q_d)]
  let Aroot : ℝ := E₀ + 1
  let Atrunc : ℝ := E₀ + 2
  have hAroot : 0 < Aroot := by dsimp [Aroot]; linarith
  have hAtrunc : 0 < Atrunc := by dsimp [Atrunc]; linarith
  obtain ⟨xPath, hxPath₂, pathExpansion⟩ :=
    path_expansion δ c₁ c₂ hδ hc₁ K F hF
  obtain ⟨Croot, xRoot, hCroot, hxRoot₂, rootReplacement⟩ :=
    root_replacement δ c₁ c₂ hδ hc₁ K F hF Aroot hAroot
  obtain ⟨Ctail, xTail, hCtail, hxTail₂, truncationAdjoint⟩ :=
    truncation_adjoint δ c₁ c₂ hδ hc₁ K F hF ρ hρ Atrunc hAtrunc
  obtain ⟨xMem, hxMem₂, memoryIdentity⟩ :=
    memory_identity δ c₁ c₂ hδ hc₁ K F hF ρ hρ
  obtain ⟨xBirth, hxBirth₂, birthBound⟩ :=
    birthDistinctness K hK F hF hHas ρ hρ
  have hratio : Filter.Tendsto (fun L : ℝ =>
      Real.exp (Real.rpow L (1 / 10 : ℝ)) /
        Real.rpow (Real.rpow L (1 / 10 : ℝ)) 20) Filter.atTop Filter.atTop :=
    (tendsto_exp_div_rpow_atTop (20 : ℝ)).comp
      (tendsto_rpow_atTop (by norm_num : 0 < (1 / 10 : ℝ)))
  have hratioEventually : ∀ᶠ L : ℝ in Filter.atTop,
      1 ≤ Real.exp (Real.rpow L (1 / 10 : ℝ)) /
        Real.rpow (Real.rpow L (1 / 10 : ℝ)) 20 :=
    hratio.eventually_ge_atTop 1
  have hgoodL : ∀ᶠ L : ℝ in Filter.atTop,
      4 ≤ L ∧ Real.rpow L 2 ≤ Real.exp (Real.rpow L (1 / 10 : ℝ)) := by
    filter_upwards [Filter.eventually_ge_atTop (4 : ℝ), hratioEventually] with L hL₄ hrat
    have hLpos : 0 < L := by linarith
    have hdenpos : 0 < Real.rpow (Real.rpow L (1 / 10 : ℝ)) 20 :=
      Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hLpos _) _
    have hdenle : Real.rpow (Real.rpow L (1 / 10 : ℝ)) 20 ≤
        Real.exp (Real.rpow L (1 / 10 : ℝ)) := (one_le_div hdenpos).mp hrat
    have hpow : Real.rpow L (2 : ℝ) = Real.rpow (Real.rpow L (1 / 10 : ℝ)) 20 := by
      calc
        Real.rpow L (2 : ℝ) = Real.rpow L ((1 / 10 : ℝ) * 20) := by congr 1 <;> norm_num
        _ = Real.rpow (Real.rpow L (1 / 10 : ℝ)) 20 := Real.rpow_mul hLpos.le _ _
    have hL2 : Real.rpow L 2 ≤ Real.exp (Real.rpow L (1 / 10 : ℝ)) := by
      rw [hpow]
      exact hdenle
    exact ⟨hL₄, hL2⟩
  have hgoodX : ∀ᶠ x : ℝ in Filter.atTop,
      4 ≤ Real.log x ∧ Real.rpow (Real.log x) 2 ≤
        Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) :=
    Real.tendsto_log_atTop.eventually hgoodL
  obtain ⟨xGrowth, hGrowth⟩ := Filter.eventually_atTop.1 hgoodX
  let Cvol : ℝ := (6 / Real.pi ^ 2) * 15
  let Csum : ℝ := Croot + Cvol * (Ctail + 1)
  let L₀ : ℝ := max 4 (max (Ctail + 1) Csum)
  let xLarge : ℝ := Real.exp L₀
  let x₀ : ℝ := max xPath
    (max xRoot (max xTail (max xMem (max xBirth (max xGrowth xLarge)))))
  have hCvol : 0 < Cvol := by
    dsimp [Cvol]
    positivity
  have hCsum : 0 < Csum := by
    dsimp [Csum]
    positivity
  have hxPath₀ : xPath ≤ x₀ := by simp [x₀]
  have hxRoot₀ : xRoot ≤ x₀ := by simp [x₀]
  have hxTail₀ : xTail ≤ x₀ := by simp [x₀]
  have hxMem₀ : xMem ≤ x₀ := by simp [x₀]
  have hxBirth₀ : xBirth ≤ x₀ := by simp [x₀]
  have hxGrowth₀ : xGrowth ≤ x₀ := by simp [x₀]
  have hxLarge₀ : xLarge ≤ x₀ := by simp [x₀]
  refine ⟨x₀, ?_, ?_⟩
  · exact le_trans hxPath₂ hxPath₀
  · intro S hS hx₀S
    let x : ℝ := S.x
    let L : ℝ := Real.log x
    have hxPathS : xPath ≤ x := le_trans hxPath₀ hx₀S
    have hxRootS : xRoot ≤ x := le_trans hxRoot₀ hx₀S
    have hxTailS : xTail ≤ x := le_trans hxTail₀ hx₀S
    have hxMemS : xMem ≤ x := le_trans hxMem₀ hx₀S
    have hxBirthS : xBirth ≤ x := le_trans hxBirth₀ hx₀S
    have hxGrowthS : xGrowth ≤ x := le_trans hxGrowth₀ hx₀S
    have hxLargeS : xLarge ≤ x := le_trans hxLarge₀ hx₀S
    have hGrowthS := hGrowth x hxGrowthS
    have hL₄ : 4 ≤ L := by simpa [L, x] using hGrowthS.1
    have hGrowthNat : L ^ 2 ≤ Real.exp (Real.rpow L (1 / 10 : ℝ)) := by
      simpa [L, x, Real.rpow_natCast] using hGrowthS.2
    have hLpos : 0 < L := by linarith
    have hLone : 1 ≤ L := by linarith
    have hL₀ : L₀ ≤ L := by
      have h := Real.log_le_log (Real.exp_pos L₀) (by simpa [xLarge, x] using hxLargeS)
      simpa [L, Real.log_exp] using h
    have hLtail : Ctail + 1 ≤ L := by
      have h : Ctail + 1 ≤ L₀ := by
        dsimp [L₀]
        exact le_trans (le_max_left _ _) (le_max_right _ _)
      exact le_trans h hL₀
    have hLsum : Csum ≤ L := by
      have h : Csum ≤ L₀ := by
        dsimp [L₀]
        exact le_trans (le_max_right _ _) (le_max_right _ _)
      exact le_trans h hL₀
    have hxpos : 0 < x := by
      have hxLarge' : Real.exp L₀ ≤ S.x := by simpa [xLarge, x] using hxLargeS
      exact lt_of_lt_of_le (Real.exp_pos L₀) hxLarge'
    have hHmLo : Real.rpow x δ ≤ S.Hm := hS.2.1
    have hHnLo : Real.rpow x δ ≤ S.Hn := hS.2.2.1
    have hHmPos : 0 < S.Hm := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos δ) hHmLo
    have hHnPos : 0 < S.Hn := lt_of_lt_of_le (Real.rpow_pos_of_pos hxpos δ) hHnLo
    have hYmem : S.Y ∈ dyadicScales x K := by simpa [x] using hS.2.2.2.2.2.1
    have hDmem : S.d₀ ∈ padScales x K := by simpa [x] using hS.2.2.2.2.2.2
    have hYpos : 0 < S.Y := by
      unfold dyadicScales at hYmem
      rcases Finset.mem_filter.mp hYmem with ⟨hImage, _⟩
      rcases Finset.mem_image.mp hImage with ⟨k, _, hYeq⟩
      calc
        0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
        _ = S.Y := hYeq
    have hD₀pos : 0 < (S.d₀ : ℝ) := by
      unfold padScales at hDmem
      rcases Finset.mem_image.mp hDmem with ⟨k, _, hk⟩
      rw [← hk]
      exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) k)
    have hUpos : 0 < S.U := by
      unfold PDScale.U PDScale.H
      exact mul_pos (mul_pos hD₀pos hYpos) hHmPos
    have hVpos : 0 < S.V := by simpa [PDScale.V] using hHnPos
    have hPathUpper : (pathLength x : ℝ) ≤ L ^ 2 := by
      have hceil (t : ℝ) (ht : 0 ≤ t) : (⌈t⌉₊ : ℝ) ≤ t + 1 := by
        calc
          (⌈t⌉₊ : ℝ) ≤ (⌊t⌋₊ : ℝ) + 1 := by exact_mod_cast Nat.ceil_le_floor_add_one t
          _ ≤ t + 1 := add_le_add (Nat.floor_le ht) le_rfl
      have hMomentR : (momentR x : ℝ) ≤ Real.rpow L (1 / 2 : ℝ) / 2 + 1 := by
        have ht : 0 ≤ Real.rpow L (1 / 2 : ℝ) / 2 :=
          div_nonneg (Real.rpow_nonneg hLpos.le _) (by norm_num)
        simpa [momentR, L, x] using hceil (Real.rpow L (1 / 2 : ℝ) / 2) ht
      have hsqrt : Real.rpow L (1 / 2 : ℝ) ≤ L := by
        calc
          Real.rpow L (1 / 2 : ℝ) ≤ Real.rpow L 1 :=
            Real.rpow_le_rpow_of_exponent_le hLone (by norm_num : (1 / 2 : ℝ) ≤ 1)
          _ = L := by simp
      calc
        (pathLength x : ℝ) = 2 * (momentR x : ℝ) := by simp [pathLength]
        _ ≤ 2 * (Real.rpow L (1 / 2 : ℝ) / 2 + 1) :=
          mul_le_mul_of_nonneg_left hMomentR (by norm_num)
        _ ≤ L + 2 := by nlinarith [hsqrt]
        _ ≤ L ^ 2 := by nlinarith [sq_nonneg (L - 2)]
    have hN₁nat : 1 ≤ pathLength x := by
      have hR : 0 < momentR x := by
        unfold momentR
        apply Nat.ceil_pos.mpr
        exact div_pos (Real.rpow_pos_of_pos hLpos _) (by norm_num)
      unfold pathLength
      omega
    have hN₁ : 1 ≤ (S.N : ℝ) := by
      change (1 : ℝ) ≤ (pathLength x : ℝ)
      exact_mod_cast hN₁nat
    have hSValid : PDScale.Valid K δ c₁ c₂ S := hS
    have hqdSqrtLt : Real.sqrt F.q_d < 1 := hsqrt₁
    have hQpos (j : ℕ) : 0 < memoryQ x F.q_d j := by
      unfold memoryQ
      split_ifs <;> positivity
    have hQlt (j : ℕ) : memoryQ x F.q_d j < 1 := by
      unfold memoryQ
      split_ifs <;> assumption
    have hEtaNonneg (j : ℕ) : 0 ≤ memoryEta x F.q_d j := by
      rw [memoryEta]
      linarith [hQlt j]
    have hEtaLeOne (j : ℕ) : memoryEta x F.q_d j ≤ 1 := by
      rw [memoryEta]
      linarith [hQpos j]
    have hBPrime (p : ℕ) (hp : p ∈ markedPrimes x K F.a) :
        0 ≤ memoryBPrime x F.q_d p ∧ memoryBPrime x F.q_d p ≤ 1 := by
      rcases Finset.mem_biUnion.mp hp with ⟨i, _, hpi⟩
      rcases Finset.mem_filter.mp hpi with ⟨_, hpiProp⟩
      rcases hpiProp with ⟨_, hpLower, _⟩
      have ha : (1 / 10 : ℝ) < F.a i := hBands.2.1 i |>.1
      have hpowBand : Real.rpow L (1 / 10 : ℝ) ≤ Real.rpow L (F.a i) :=
        Real.rpow_le_rpow_of_exponent_le hLone ha.le
      have hpExp : Real.exp (Real.rpow L (1 / 10 : ℝ)) ≤ (p : ℝ) :=
        (Real.exp_le_exp.mpr hpowBand).trans hpLower
      have hpPath : (pathLength x : ℝ) ≤ (p : ℝ) :=
        hPathUpper.trans (hGrowthNat.trans hpExp)
      have hnum : ((pathLength x + 1 : ℕ) : ℝ) ≤ (p : ℝ) + 1 := by
        exact_mod_cast Nat.succ_le_succ (show pathLength x ≤ p by exact_mod_cast hpPath)
      have hfrac : ((pathLength x + 1 : ℕ) : ℝ) / ((p : ℝ) + 1) ≤ 1 :=
        (div_le_one (by positivity)).2 hnum
      have hpnonneg : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
      have hdennonneg : 0 ≤ (p : ℝ) + 1 := add_nonneg hpnonneg (by norm_num)
      have hsum :
          (∑ j ∈ Finset.range (pathLength x + 1),
            memoryEta x F.q_d j / ((p : ℝ) + 1)) ≤ 1 := by
        calc
          _ ≤ ∑ j ∈ Finset.range (pathLength x + 1), (1 : ℝ) / ((p : ℝ) + 1) := by
            apply Finset.sum_le_sum
            intro j hj
            exact div_le_div_of_nonneg_right (hEtaLeOne j) hdennonneg
          _ = ((pathLength x + 1 : ℕ) : ℝ) / ((p : ℝ) + 1) := by
            simp [div_eq_mul_inv]
          _ ≤ 1 := hfrac
      have hsumNonneg :
          0 ≤ ∑ j ∈ Finset.range (pathLength x + 1),
            memoryEta x F.q_d j / ((p : ℝ) + 1) := by
        calc
          0 = ∑ j ∈ Finset.range (pathLength x + 1), (0 : ℝ) := by simp
          _ ≤ ∑ j ∈ Finset.range (pathLength x + 1),
                memoryEta x F.q_d j / ((p : ℝ) + 1) := by
            apply Finset.sum_le_sum
            intro j hj
            exact div_nonneg (hEtaNonneg j) hdennonneg
      unfold memoryBPrime
      constructor
      · exact sub_nonneg.mpr hsum
      · exact sub_le_self _ hsumNonneg
    have hBaseBounds : 0 ≤ memoryBaseline F S ∧ memoryBaseline F S ≤ 1 := by
      unfold memoryBaseline
      constructor
      · exact Finset.prod_nonneg fun p hp => (hBPrime p hp).1
      · exact Finset.prod_le_one₀
          (fun p hp => (hBPrime p hp).1) (fun p hp => (hBPrime p hp).2)
    have hBaseNorm : ‖(memoryBaseline F S : ℂ)‖ ≤ 1 := by
      calc
        ‖(memoryBaseline F S : ℂ)‖ = |memoryBaseline F S| := by
          simp [Complex.norm_real, Real.norm_eq_abs]
        _ = memoryBaseline F S := abs_of_nonneg hBaseBounds.1
        _ ≤ 1 := hBaseBounds.2
    have htruncBound : ∀ w : ArchRoot, w.InRegion S →
        ‖historyDistinct F S ρ w - historyDistinctTrunc F S ρ w‖ ≤
          Ctail * Real.rpow S.L (-(E₀ + 2) * (S.N : ℝ)) := by
      intro w hw
      simpa [Atrunc] using truncationAdjoint S hSValid (le_trans hxTail₀ hx₀S) w hw
    have hbirthBoundAtScale : ∀ w : ArchRoot, w.InRegion S →
        ‖historyDistinctTrunc F S ρ w‖ ≤
          Real.rpow S.L (-(E₀ + 2) * (S.N : ℝ)) := by
      intro w hw
      exact birthBound S hSValid (le_trans hxBirth₀ hx₀S) w hw
    have hhistory : ∀ w : ArchRoot, w.InRegion S →
        ‖historyDistinct F S ρ w‖ ≤
          (Ctail + 1) * Real.rpow S.L (-(E₀ + 2) * (S.N : ℝ)) := by
      intro w hw
      have ht := htruncBound w hw
      have hb := hbirthBoundAtScale w hw
      have heq : historyDistinct F S ρ w =
          (historyDistinct F S ρ w - historyDistinctTrunc F S ρ w) +
            historyDistinctTrunc F S ρ w := by ring
      rw [heq]
      calc
        ‖(historyDistinct F S ρ w - historyDistinctTrunc F S ρ w) +
            historyDistinctTrunc F S ρ w‖ ≤
          ‖historyDistinct F S ρ w - historyDistinctTrunc F S ρ w‖ +
            ‖historyDistinctTrunc F S ρ w‖ := norm_add_le _ _
        _ ≤ Ctail * Real.rpow S.L (-(E₀ + 2) * (S.N : ℝ)) +
              Real.rpow S.L (-(E₀ + 2) * (S.N : ℝ)) := add_le_add ht hb
        _ = (Ctail + 1) * Real.rpow S.L (-(E₀ + 2) * (S.N : ℝ)) := by ring
    let D : ℝ := (Ctail + 1) * Real.rpow L (-(E₀ + 2) * (S.N : ℝ))
    have hDnonneg : 0 ≤ D := by
      dsimp [D]
      positivity
    have hline (u v r : ℝ) (hu₁ : 1 ≤ u) (hu₂ : u ≤ 16)
        (hv₁ : 1 ≤ v) (hv₂ : v ≤ 2) (hr₁ : 0 ≤ r) (hr₂ : r ≤ 1) :
        ‖lineAverage (fun ℓ => envMomentC F S ⟨S.U * u, S.V * v, r⟩ ℓ)‖ ≤ D := by
      let w : ArchRoot := ⟨S.U * u, S.V * v, r⟩
      have hw : w.InRegion S := by
        change S.U ≤ S.U * u ∧ S.U * u ≤ 16 * S.U ∧
          S.V ≤ S.V * v ∧ S.V * v ≤ 2 * S.V ∧ 0 ≤ r ∧ r ≤ 1
        constructor
        · calc
            S.U = S.U * 1 := by ring
            _ ≤ S.U * u := mul_le_mul_of_nonneg_left hu₁ hUpos.le
        constructor
        · calc
            S.U * u ≤ S.U * 16 := mul_le_mul_of_nonneg_left hu₂ hUpos.le
            _ = 16 * S.U := by ring
        constructor
        · calc
            S.V = S.V * 1 := by ring
            _ ≤ S.V * v := mul_le_mul_of_nonneg_left hv₁ hVpos.le
        constructor
        · calc
            S.V * v ≤ S.V * 2 := mul_le_mul_of_nonneg_left hv₂ hVpos.le
            _ = 2 * S.V := by ring
        exact ⟨hr₁, hr₂⟩
      have hid := memoryIdentity S hSValid (le_trans hxMem₀ hx₀S) w (by simpa [w] using hw)
      have hh := hhistory w (by simpa [w] using hw)
      calc
        ‖lineAverage (fun ℓ => envMomentC F S ⟨S.U * u, S.V * v, r⟩ ℓ)‖ =
            ‖(memoryBaseline F S : ℂ) * historyDistinct F S ρ w‖ := by
              rw [hid]
        _ = ‖(memoryBaseline F S : ℂ)‖ * ‖historyDistinct F S ρ w‖ := norm_mul _ _
        _ ≤ 1 * ((Ctail + 1) * Real.rpow S.L (-(E₀ + 2) * (S.N : ℝ))) :=
          mul_le_mul hBaseNorm hh (norm_nonneg _) (by norm_num)
        _ = D := by simp [D, L, x, PDScale.L]
    let f : ℝ → ℝ → ℝ → ℝ := fun u v r =>
      (lineAverage (fun ℓ => envMomentC F S ⟨S.U * u, S.V * v, r⟩ ℓ)).re
    have hR (u v : ℝ) (hu₁ : 1 ≤ u) (hu₂ : u ≤ 16)
        (hv₁ : 1 ≤ v) (hv₂ : v ≤ 2) :
        |∫ r in (0 : ℝ)..1, f u v r| ≤ D := by
      have hnorm : ‖∫ r in (0 : ℝ)..1, f u v r‖ ≤ D * |(1 : ℝ) - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (a := (0 : ℝ)) (b := (1 : ℝ)) (f := fun r => f u v r) (C := D) (by
        intro r hr
        have hrIoc : r ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa only [Set.uIoc_of_le (a := (0 : ℝ)) (b := (1 : ℝ))
            (by norm_num : (0 : ℝ) ≤ 1)] using hr
        have hpoint := hline u v r hu₁ hu₂ hv₁ hv₂ hrIoc.1.le hrIoc.2
        calc
          ‖f u v r‖ = |(lineAverage
              (fun ℓ => envMomentC F S ⟨S.U * u, S.V * v, r⟩ ℓ)).re| := by
                simp [f, Real.norm_eq_abs]
          _ ≤ ‖lineAverage
              (fun ℓ => envMomentC F S ⟨S.U * u, S.V * v, r⟩ ℓ)‖ :=
                Complex.abs_re_le_norm _
          _ ≤ D := hpoint)
      calc
        |∫ r in (0 : ℝ)..1, f u v r| = ‖∫ r in (0 : ℝ)..1, f u v r‖ :=
          (Real.norm_eq_abs _).symm
        _ ≤ D * |(1 : ℝ) - 0| := hnorm
        _ = D := by norm_num
    have hV (u : ℝ) (hu₁ : 1 ≤ u) (hu₂ : u ≤ 16) :
        |∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, f u v r| ≤ D := by
      have hnorm : ‖∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, f u v r‖ ≤
          D * |(2 : ℝ) - 1| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (a := (1 : ℝ)) (b := (2 : ℝ)) (f := fun v => ∫ r in (0 : ℝ)..1, f u v r)
          (C := D) (by
        intro v hv
        have hvIoc : v ∈ Set.Ioc (1 : ℝ) 2 := by
          simpa only [Set.uIoc_of_le (a := (1 : ℝ)) (b := (2 : ℝ))
            (by norm_num : (1 : ℝ) ≤ 2)] using hv
        have hpoint := hR u v hu₁ hu₂ hvIoc.1.le hvIoc.2
        simpa [Real.norm_eq_abs] using hpoint)
      calc
        |∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, f u v r| =
            ‖∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, f u v r‖ :=
              (Real.norm_eq_abs _).symm
        _ ≤ D * |(2 : ℝ) - 1| := hnorm
        _ = D := by norm_num
    have hOuter :
        |∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, f u v r| ≤ 15 * D := by
      have hnorm : ‖∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2,
          ∫ r in (0 : ℝ)..1, f u v r‖ ≤ D * |(16 : ℝ) - 1| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (a := (1 : ℝ)) (b := (16 : ℝ))
          (f := fun u => ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, f u v r)
          (C := D) (by
        intro u hu
        have huIoc : u ∈ Set.Ioc (1 : ℝ) 16 := by
          simpa only [Set.uIoc_of_le (a := (1 : ℝ)) (b := (16 : ℝ))
            (by norm_num : (1 : ℝ) ≤ 16)] using hu
        have hpoint := hV u huIoc.1.le huIoc.2
        simpa [Real.norm_eq_abs] using hpoint)
      calc
        |∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, f u v r| =
            ‖∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1, f u v r‖ :=
              (Real.norm_eq_abs _).symm
        _ ≤ D * |16 - 1| := hnorm
        _ = 15 * D := by ring
    have hModel : |modelRootAverage F S| ≤ Cvol * D := by
      have hOuterModel :
          |∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1,
              (lineAverage (fun ℓ => envMomentC F S ⟨S.U * u, S.V * v, r⟩ ℓ)).re| ≤ 15 * D := by
        simpa [f] using hOuter
      have hfactor : 0 ≤ 6 / Real.pi ^ 2 := by positivity
      dsimp [modelRootAverage, Cvol]
      calc
        |(6 / Real.pi ^ 2) *
            (∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1,
              (lineAverage (fun ℓ => envMomentC F S ⟨S.U * u, S.V * v, r⟩ ℓ)).re)| =
            (6 / Real.pi ^ 2) *
              |∫ u in (1 : ℝ)..16, ∫ v in (1 : ℝ)..2, ∫ r in (0 : ℝ)..1,
                (lineAverage (fun ℓ => envMomentC F S ⟨S.U * u, S.V * v, r⟩ ℓ)).re| := by
                  rw [abs_mul, abs_of_nonneg hfactor]
        _ ≤ (6 / Real.pi ^ 2) * (15 * D) :=
          mul_le_mul_of_nonneg_left hOuterModel hfactor
        _ = (6 / Real.pi ^ 2 * 15) * D := by ring
    have hpowSaving :
        Real.rpow L (-(E₀ + 2) * (S.N : ℝ)) ≤
          Real.rpow L (-(E₀ + 1) * (S.N : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le hLone
      have hNnonneg : 0 ≤ (S.N : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hModelSaving : |modelRootAverage F S| ≤
        Cvol * (Ctail + 1) * Real.rpow L (-(E₀ + 1) * (S.N : ℝ)) := by
      dsimp [D] at hModel
      have htailNonneg : 0 ≤ Ctail + 1 := by positivity
      calc
        |modelRootAverage F S| ≤ Cvol * ((Ctail + 1) *
            Real.rpow L (-(E₀ + 2) * (S.N : ℝ))) := hModel
        _ ≤ Cvol * ((Ctail + 1) *
            Real.rpow L (-(E₀ + 1) * (S.N : ℝ))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hpowSaving htailNonneg) hCvol.le
        _ = Cvol * (Ctail + 1) *
            Real.rpow L (-(E₀ + 1) * (S.N : ℝ)) := by ring
    have hroot := rootReplacement S hSValid (le_trans hxRoot₀ hx₀S)
    have hphysical : detMoment F S ≤
        modelRootAverage F S + Croot * Real.rpow L (-(E₀ + 1) * (S.N : ℝ)) := by
      rw [pathExpansion S hSValid (le_trans hxPath₀ hx₀S)]
      have hdiff := le_abs_self
        (physicalRootAverage F S - modelRootAverage F S)
      have hbound : |physicalRootAverage F S - modelRootAverage F S| ≤
          Croot * Real.rpow L (-(E₀ + 1) * (S.N : ℝ)) := by
        simpa [Aroot, L, x, PDScale.L] using hroot
      linarith
    have hsumBound : detMoment F S ≤ Csum *
        Real.rpow L (-(E₀ + 1) * (S.N : ℝ)) := by
      have hmodelLe := le_abs_self (modelRootAverage F S)
      calc
        detMoment F S ≤ modelRootAverage F S +
            Croot * Real.rpow L (-(E₀ + 1) * (S.N : ℝ)) := hphysical
        _ ≤ |modelRootAverage F S| +
            Croot * Real.rpow L (-(E₀ + 1) * (S.N : ℝ)) := by
              exact add_le_add hmodelLe le_rfl
        _ ≤ Cvol * (Ctail + 1) * Real.rpow L (-(E₀ + 1) * (S.N : ℝ)) +
              Croot * Real.rpow L (-(E₀ + 1) * (S.N : ℝ)) :=
                add_le_add hModelSaving le_rfl
        _ = Csum * Real.rpow L (-(E₀ + 1) * (S.N : ℝ)) := by
              dsimp [Csum]
              ring
    have hCsumLe : Csum ≤ Real.rpow L (S.N : ℝ) := by
      calc
        Csum ≤ L := hLsum
        _ = Real.rpow L 1 := by simp
        _ ≤ Real.rpow L (S.N : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hLone hN₁
    have hpowAdd : Real.rpow L (-(E₀ + 1) * (S.N : ℝ)) *
        Real.rpow L (S.N : ℝ) = Real.rpow L (-E₀ * (S.N : ℝ)) := by
      calc
        Real.rpow L (-(E₀ + 1) * (S.N : ℝ)) * Real.rpow L (S.N : ℝ) =
            Real.rpow L ((-(E₀ + 1) * (S.N : ℝ)) + (S.N : ℝ)) :=
              (Real.rpow_add hLpos _ _).symm
        _ = Real.rpow L (-E₀ * (S.N : ℝ)) := by congr 1 <;> ring
    calc
      detMoment F S ≤ Csum * Real.rpow L (-(E₀ + 1) * (S.N : ℝ)) := hsumBound
      _ ≤ Real.rpow L (S.N : ℝ) *
            Real.rpow L (-(E₀ + 1) * (S.N : ℝ)) :=
          mul_le_mul_of_nonneg_right hCsumLe (Real.rpow_nonneg (le_of_lt hLpos) _)
      _ = Real.rpow L (-(E₀ + 1) * (S.N : ℝ)) * Real.rpow L (S.N : ℝ) := by ring
      _ = Real.rpow L (-E₀ * (S.N : ℝ)) := hpowAdd

/-- `prop:minor-moment` (replacement part, mem:replacement-interface) — PD 04:22-34.  REPLACES the
second conjunct of the frozen `minor_moment`.  For every `A` choose `E₀ > A + C_e + 3`, then
`A₀, K₀` from `minor_moment`: `|Q_Y - Q_Y^{maj}| ≪_A XY L^{-A}`.  Only the coefficient bounds of
the family enter (no long-coefficient hypothesis).  Proof: `minor_moment`,
`moment_to_pairing`, `strip_goodness_pads`, `#padScales ≪_K L^{0.21}`. -/
theorem minor_replacement (δ C c₁ c₂ : ℝ) (hδ : 0 < δ) (hC : 0 < C) (hc₁ : 0 < c₁)
    (hc₁₂ : c₁ ≤ c₂) (q_d : ℝ) (eta psi : ℝ → ℝ) :
    ∀ A : ℝ, 0 < A → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ,
      ∀ (K : ℕ), K₀ ≤ K → ∀ (F : PDFix K), F.Valid → F.Has q_d A₀ eta psi →
        ∀ family : CoefficientFamily δ C c₁ c₂,
          ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
            ∀ beta : ℕ → ℂ, IsFamilySecondCoefficient family x beta →
              ∀ Y ∈ dyadicScales x K,
                ‖(cauchySquare x K F.a Y family beta F.eta : ℂ) -
                    majorArcSum x K F.a Y F.A₀ family beta F.eta F.psi‖ ≤
                  C_A * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A) := by
  intro A hA
  obtain ⟨C_e, hC_e, momentToPairing⟩ :=
    moment_to_pairing δ C c₁ c₂ hδ hC hc₁ hc₁₂
  let E₀ : ℝ := A + C_e + 1
  have hE₀ : 0 < E₀ := by
    dsimp [E₀]
    linarith
  obtain ⟨A₀, hA₀, K₀, minorMoment⟩ :=
    minor_moment δ c₁ c₂ hδ hc₁ q_d eta psi E₀ hE₀
  refine ⟨A₀, hA₀, K₀, ?_⟩
  intro K hK F hF hHas family
  obtain ⟨xₘ, hxₘ₂, momentBound⟩ := minorMoment K hK F hF hHas
  obtain ⟨Cpair, xₚ, hCpair, hxₚ₂, pairingBound⟩ := momentToPairing K F hF
  obtain ⟨Cstrip, xₛ, hCstrip, hxₛ₂, stripBound⟩ :=
    strip_goodness_pads δ C c₁ c₂ hδ hC hc₁ K F hF A hA
  let Ccard : ℝ := ((K + 1 : ℕ) : ℝ) + 1
  let xBase : ℝ := max xₘ (max xₚ (max xₛ (Real.exp 1)))
  let x₀ : ℝ := max family.xMin xBase
  have hCcard : 0 < Ccard := by
    dsimp [Ccard]
    positivity
  refine Exists.intro (Ccard * Cpair + Cstrip) ?_
  refine Exists.intro x₀ ?_
  constructor
  · positivity
  constructor
  · have hx₀ₘ : xₘ ≤ x₀ := by
      have hx₀Base : xBase ≤ x₀ := by simp [x₀]
      have hxₘBase : xₘ ≤ xBase := by simp [xBase]
      exact le_trans hxₘBase hx₀Base
    exact le_trans hxₘ₂ hx₀ₘ
  · intro x hx₀x beta hbeta Y hY
    have hx₀Base : xBase ≤ x₀ := by simp [x₀]
    have hfamilyMin₀ : family.xMin ≤ x₀ := by simp [x₀]
    have hx₀ₘ : xₘ ≤ x₀ := by
      exact le_trans (by simp [xBase]) hx₀Base
    have hx₀ₚ : xₚ ≤ x₀ := by
      exact le_trans (by simp [xBase]) hx₀Base
    have hx₀ₛ : xₛ ≤ x₀ := by
      exact le_trans (by simp [xBase]) hx₀Base
    have hx₀exp : Real.exp 1 ≤ x₀ := by
      exact le_trans (by simp [xBase]) hx₀Base
    have hxₘx : xₘ ≤ x := le_trans hx₀ₘ hx₀x
    have hxₚx : xₚ ≤ x := le_trans hx₀ₚ hx₀x
    have hxₛx : xₛ ≤ x := le_trans hx₀ₛ hx₀x
    have hfamilyMin : family.xMin ≤ x := le_trans hfamilyMin₀ hx₀x
    have hx₂ : 2 ≤ x := le_trans hxₘ₂ hxₘx
    have hxexp : Real.exp 1 ≤ x := le_trans hx₀exp hx₀x
    have hlog : 1 ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 1) hxexp
      simpa using h
    have hlogpos : 0 < Real.log x := lt_of_lt_of_le (by norm_num) hlog
    have hpowCard : Real.rpow (Real.log x) (21 / 100 : ℝ) ≤ Real.log x := by
      calc
        Real.rpow (Real.log x) (21 / 100 : ℝ) ≤ Real.rpow (Real.log x) 1 :=
          Real.rpow_le_rpow_of_exponent_le hlog (by norm_num)
        _ = Real.log x := by simp
    let u : ℝ := ((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ)
    have huEq : u = ((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ) := rfl
    have hu : 0 ≤ u := by
      dsimp [u]
      positivity
    have hfloor : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu
    have hcardNat : (padScales x K).card ≤ ⌊u⌋₊ + 1 := by
      unfold padScales
      rw [← huEq]
      calc
        ((Finset.range (⌊u⌋₊ + 1)).image (fun k => 2 ^ k)).card ≤
            (Finset.range (⌊u⌋₊ + 1)).card := Finset.card_image_le
        _ = ⌊u⌋₊ + 1 := by simp
    have hcard : ((padScales x K).card : ℝ) ≤ Ccard * Real.log x := by
      calc
        ((padScales x K).card : ℝ) ≤ (⌊u⌋₊ : ℝ) + 1 := by exact_mod_cast hcardNat
        _ ≤ u + 1 := add_le_add hfloor le_rfl
        _ ≤ Ccard * Real.log x := by
          dsimp [u, Ccard]
          calc
            ((K + 1 : ℕ) : ℝ) * Real.rpow (Real.log x) (21 / 100 : ℝ) + 1 ≤
                ((K + 1 : ℕ) : ℝ) * Real.log x + Real.log x := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hpowCard (by positivity)) hlog
            _ = (((K + 1 : ℕ) : ℝ) + 1) * Real.log x := by ring
    have hxX : 0 < family.Hm x * family.Hn x := by
      rcases family.scales x hfamilyMin with ⟨hHm, hHn, _, _⟩
      have hxpos : 0 < x := by linarith
      have hp : 0 < Real.rpow x δ := Real.rpow_pos_of_pos hxpos δ
      exact mul_pos (lt_of_lt_of_le hp hHm) (lt_of_lt_of_le hp hHn)
    have hYpos : 0 < Y := by
      unfold dyadicScales at hY
      rcases Finset.mem_filter.mp hY with ⟨hImage, _⟩
      rcases Finset.mem_image.mp hImage with ⟨k, _, rfl⟩
      exact pow_pos (by norm_num : 0 < (2 : ℝ)) k
    have hScaleValid (d₀ : ℕ) (hd₀ : d₀ ∈ padScales x K) :
        (familyScale family x Y d₀).Valid K δ c₁ c₂ := by
      rcases family.scales x hfamilyMin with ⟨hHm, hHn, hprodLo, hprodHi⟩
      dsimp [PDScale.Valid, familyScale]
      exact ⟨hx₂, hHm, hHn, hprodLo, hprodHi, hY, hd₀⟩
    have hFamilyAt (d₀ : ℕ) : FamilyAtScale family (familyScale family x Y d₀) := by
      constructor <;> rfl
    have hBetaAt (d₀ : ℕ) : IsSecondCoefficient (familyScale family x Y d₀) C beta := by
      simpa [IsSecondCoefficient, IsFamilySecondCoefficient, familyScale] using hbeta
    have hPairHyp : ∀ d₀ ∈ padScales x K,
        ‖detPairing F (familyScale family x Y d₀) family beta‖ ≤
          Cpair * (familyScale family x Y d₀).U * (familyScale family x Y d₀).V *
            Real.rpow (Real.log x) (-E₀ + C_e) := by
      intro d₀ hd₀
      have hvalid := hScaleValid d₀ hd₀
      have hmoment := momentBound (familyScale family x Y d₀) hvalid hxₘx
      exact pairingBound (familyScale family x Y d₀) hvalid hxₚx family (hFamilyAt d₀)
        hfamilyMin beta (hBetaAt d₀) E₀ hE₀ hmoment
    have hstrip := stripBound x hxₛx family hfamilyMin beta hbeta Y hY E₀ C_e Cpair hPairHyp
    have hExp : -E₀ + C_e = -A - 1 := by
      dsimp [E₀]
      ring
    have hPow : Real.log x * Real.rpow (Real.log x) (-A - 1) =
        Real.rpow (Real.log x) (-A) := by
      calc
        Real.log x * Real.rpow (Real.log x) (-A - 1) =
            Real.rpow (Real.log x) (-A - 1) * Real.log x := by ring
        _ = Real.rpow (Real.log x) ((-A - 1) + 1) :=
          (Real.rpow_add_one (ne_of_gt hlogpos) (-A - 1)).symm
        _ = Real.rpow (Real.log x) (-A) := by congr 1 <;> ring
    have hMain :
        ((padScales x K).card : ℝ) * Cpair * (family.Hm x * family.Hn x) * Y *
            Real.rpow (Real.log x) (-E₀ + C_e) ≤
          Ccard * Cpair * (family.Hm x * family.Hn x) * Y *
            Real.rpow (Real.log x) (-A) := by
      rw [hExp]
      have hpowPos : 0 < Real.rpow (Real.log x) (-A - 1) :=
        Real.rpow_pos_of_pos hlogpos _
      have hfac : 0 ≤ Cpair * (family.Hm x * family.Hn x) * Y *
          Real.rpow (Real.log x) (-A - 1) :=
        le_of_lt (mul_pos (mul_pos (mul_pos hCpair hxX) hYpos) hpowPos)
      calc
        _ = ((padScales x K).card : ℝ) *
              (Cpair * (family.Hm x * family.Hn x) * Y *
                Real.rpow (Real.log x) (-A - 1)) := by ring
        _ ≤ (Ccard * Real.log x) *
              (Cpair * (family.Hm x * family.Hn x) * Y *
                Real.rpow (Real.log x) (-A - 1)) :=
          mul_le_mul_of_nonneg_right hcard hfac
        _ = Ccard * Cpair * (family.Hm x * family.Hn x) * Y *
              (Real.log x * Real.rpow (Real.log x) (-A - 1)) := by ring
        _ = Ccard * Cpair * (family.Hm x * family.Hn x) * Y *
              Real.rpow (Real.log x) (-A) := by rw [hPow]
    calc
      ‖(cauchySquare x K F.a Y family beta F.eta : ℂ) -
          majorArcSum x K F.a Y F.A₀ family beta F.eta F.psi‖ ≤
          ((padScales x K).card : ℝ) * Cpair * (family.Hm x * family.Hn x) * Y *
              Real.rpow (Real.log x) (-E₀ + C_e) +
            Cstrip * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A) := hstrip
      _ ≤ Ccard * Cpair * (family.Hm x * family.Hn x) * Y *
              Real.rpow (Real.log x) (-A) +
            Cstrip * (family.Hm x * family.Hn x) * Y * Real.rpow (Real.log x) (-A) :=
          add_le_add hMain le_rfl
      _ = (Ccard * Cpair + Cstrip) * (family.Hm x * family.Hn x) * Y *
            Real.rpow (Real.log x) (-A) := by ring


end

end ArtinPrimitiveRoots.TypeII.PD
