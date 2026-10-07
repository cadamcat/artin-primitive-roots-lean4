import ArtinPrimitiveRoots.TypeII.PD.Memory
import ArtinPrimitiveRoots.TypeII.PD.Determinant
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.Symmetry
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadProbability
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
  sorry

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
  sorry

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
  sorry

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

private theorem stateRoot_eq_rootC_div {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    {H' Hm Hn : ℝ} (P : PhysicalState x K a H' Hm Hn) (hfirst : 2 ≤ P.first) :
    stateRoot P = (rootC P.first P.second : ℝ) / (P.first : ℝ) := by
  unfold stateRoot
  rw [physical_completionC_eq_rootC P hfirst]
  congr 1

private theorem physicalState_envValid {K : ℕ} (F : PDFix K) (S : PDScale)
    (P : PState F S) : EnvValid F S (P.pos, P.labels) := by
  unfold EnvValid
  refine ⟨?_, ?_⟩
  · change Int.gcd (P.first : ℤ) (P.second : ℤ) = 1
    rw [Int.gcd_natCast_natCast]
    exact P.primitive.gcd_eq_one
  · constructor
    · intro i j
      exact ⟨P.label_prime i j, P.label_in_band i j⟩
    · exact P.label_distinct

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

private theorem detPairing_goodExpansion {K : ℕ} (F : PDFix K) (S : PDScale)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    [Fintype (PState F S)] :
    detPairing F S family beta =
      (physicalMeasure S.x K F.a : ℂ) *
        ∑ P : PState F S,
          (endpointF S.x K F.a family beta P *
            (if IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a P.labels (stateRoot P)
              then (1 : ℂ) else 0)) *
            ∑ Q : PState F S,
              physRowKernel F S P Q *
                physGood F S
                  (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta) Q := by
  classical
  let gGood : PState F S → ℂ := fun Q =>
    physGood F S (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta) Q
  let row : PState F S → ℂ := fun P =>
    ∑ Q : PState F S, physRowKernel F S P Q * gGood Q
  let w : PState F S → ℂ := fun P =>
    endpointF S.x K F.a family beta P *
      (if IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a P.labels (stateRoot P)
        then (1 : ℂ) else 0)
  have hGoodSym : physSym F S
      (physGood F S (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta)) = gGood := by
    funext Q
    exact physSym_goodEndpointG F S family beta Q
  have hw : ∀ (P : PState F S) (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))),
      w (P.permute σ) = w P := by
    intro P σ
    simp [w, endpointF_permute, isGoodRatio_statePermute]
  have houter :
      (∑ P : PState F S,
        endpointF S.x K F.a family beta P *
          physGood F S (physSym F S row) P) =
        ∑ P : PState F S, w P * row P := by
    calc
      _ = ∑ P : PState F S, w P * physSym F S row P := by
        apply Finset.sum_congr rfl
        intro P hP
        by_cases hgood : IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a P.labels (stateRoot P)
        · simp [w, physGood, hgood]
        · simp [w, physGood, hgood]
      _ = _ := sum_mul_physSym_eq_of_permuteInvariant F S w row hw
  rw [detPairing_finiteDoubleSum, hGoodSym]
  change (physicalMeasure S.x K F.a : ℂ) *
      (∑ P : PState F S,
        endpointF S.x K F.a family beta P *
          physGood F S (physSym F S row) P) = _
  rw [houter]

private theorem detPairing_noGoodExpansion {K : ℕ} (F : PDFix K) (S : PDScale)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    [Fintype (PState F S)] :
    detPairingNoGood F S family beta =
      (physicalMeasure S.x K F.a : ℂ) *
        ∑ P : PState F S,
          endpointF S.x K F.a family beta P *
            ∑ Q : PState F S,
              physRowKernel F S P Q * endpointG S.x K F.a family beta Q := by
  classical
  let row : PState F S → ℂ := fun P =>
    ∑ Q : PState F S,
      physRowKernel F S P Q * endpointG S.x K F.a family beta Q
  have hGsym : physSym F S
      (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta) =
        endpointGVector S.x K F.a S.H S.Hm S.Hn family beta := by
    funext Q
    exact physSym_endpointG F S family beta Q
  have hw : ∀ (P : PState F S) (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))),
      endpointF S.x K F.a family beta (P.permute σ) =
        endpointF S.x K F.a family beta P := by
    intro P σ
    exact endpointF_permute family beta P σ
  have houter :
      (∑ P : PState F S,
        endpointF S.x K F.a family beta P * physSym F S row P) =
        ∑ P : PState F S, endpointF S.x K F.a family beta P * row P :=
    sum_mul_physSym_eq_of_permuteInvariant F S _ row hw
  rw [detPairingNoGood_finiteDoubleSum, hGsym]
  change (physicalMeasure S.x K F.a : ℂ) *
      (∑ P : PState F S,
        endpointF S.x K F.a family beta P * physSym F S row P) = _
  rw [houter]

private theorem detPairing_difference_expansion {K : ℕ} (F : PDFix K) (S : PDScale)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    [Fintype (PState F S)] :
    detPairing F S family beta - detPairingNoGood F S family beta =
      (physicalMeasure S.x K F.a : ℂ) *
        ((∑ P : PState F S,
          (endpointF S.x K F.a family beta P *
            (if IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a P.labels (stateRoot P)
              then (1 : ℂ) else 0)) *
            ∑ Q : PState F S,
              physRowKernel F S P Q *
                physGood F S
                  (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta) Q) -
        ∑ P : PState F S,
          endpointF S.x K F.a family beta P *
            ∑ Q : PState F S,
              physRowKernel F S P Q * endpointG S.x K F.a family beta Q) := by
  rw [detPairing_goodExpansion, detPairing_noGoodExpansion]
  ring

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
  intro K F hF A hA
  by_cases hc₂ : 0 < c₂
  · have hBands : ValidBands K F.a := hF.1
    have hε : 0 < Real.log 2 / 2 := by positivity
    have hBandEvent : ∀ᶠ x : ℝ in atTop, ∀ i : Fin K,
        Real.log 2 / 2 ≤ bandMass x (F.a i) ∧ 0 < bandMass x (F.a i) := by
      rw [Filter.eventually_all]
      intro i
      have ha₀ : 0 < F.a i := lt_trans (by norm_num : (0 : ℝ) < 1 / 10)
        (hBands.2.1 i).1
      have ha₁ : F.a i < 1 := lt_trans (hBands.2.1 i).2
        (by norm_num : (1 / 5 : ℝ) < 1)
      obtain ⟨xBand, hxBand₂, hMass⟩ :=
        band_mass (F.a i) ha₀ ha₁ (Real.log 2 / 2) hε
      filter_upwards [Filter.eventually_ge_atTop xBand] with x hx
      refine ⟨?_, (hMass x hx).2⟩
      have habs := abs_le.mp (hMass x hx).1
      linarith
    obtain ⟨xBand, hBandEvent⟩ := Filter.eventually_atTop.mp hBandEvent
    let εgrid : ℝ := min (δ / 10000) (1 / 100)
    have hεgrid : 0 < εgrid := by
      dsimp [εgrid]
      exact lt_min (by positivity) (by norm_num)
    have hεgrid_lt : εgrid < 1 := by
      dsimp [εgrid]
      exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    let CrootScale : ℝ := 4 * (K : ℝ) + 1
    have hCrootScale : 0 < CrootScale := by positivity
    obtain ⟨cδ, Croot, xRoot, hcδ, hCroot, hxRoot₂, rootLines⟩ :=
      root_lines δ CrootScale hδ hCrootScale
    obtain ⟨xBoundary, hxBoundary₂, rootBoundary⟩ :=
      root_arch_boundary δ c₁ c₂ hδ hc₁ K F hF εgrid hεgrid hεgrid_lt
    obtain ⟨cGood, xGood, hcGood, hxGood₂, goodState⟩ := good_state K F.a hBands
    obtain ⟨xDisjoint, hxDisjoint₂, bandsDisjoint⟩ :=
      validBands_disjoint_eventually K F.a hBands
    let x₀ : ℝ :=
      max (Real.exp 1) (max 2 (max xBand (max xRoot (max xBoundary (max xGood xDisjoint)))))
    have hx₀₂ : 2 ≤ x₀ := by simp [x₀]
    have hx₀Exp : Real.exp 1 ≤ x₀ := by simp [x₀]
    have hx₀Band : xBand ≤ x₀ := by simp [x₀]
    have hx₀Root : xRoot ≤ x₀ := by simp [x₀]
    have hx₀Boundary : xBoundary ≤ x₀ := by simp [x₀]
    have hx₀Good : xGood ≤ x₀ := by simp [x₀]
    have hx₀Disjoint : xDisjoint ≤ x₀ := by simp [x₀]
    refine ⟨1, x₀, by norm_num, hx₀₂, ?_⟩
    intro S hS hx family hFamilyAt hFamilyMin beta hbeta
    have hxBand : xBand ≤ S.x := le_trans hx₀Band hx
    have hxRoot : xRoot ≤ S.x := le_trans hx₀Root hx
    have hxBoundary : xBoundary ≤ S.x := le_trans hx₀Boundary hx
    have hxGood : xGood ≤ S.x := le_trans hx₀Good hx
    have hxDisjoint : xDisjoint ≤ S.x := le_trans hx₀Disjoint hx
    have hBandsDisjoint := bandsDisjoint S.x hxDisjoint
    have hxExp : Real.exp 1 ≤ S.x := le_trans hx₀Exp hx
    have hlogone : 1 ≤ Real.log S.x := by
      have h := Real.log_le_log (Real.exp_pos 1) hxExp
      simpa using h
    have hBandMass : ∀ i, Real.log 2 / 2 ≤ bandMass S.x (F.a i) := fun i =>
      (hBandEvent S.x hxBand i).1
    have hBandMassPos : ∀ i, 0 < bandMass S.x (F.a i) := fun i =>
      (hBandEvent S.x hxBand i).2
    rcases hS with ⟨hx₂, hHmLo, hHnLo, hXLo, hXHi, hYmem, hDmem⟩
    have hxpos : 0 < S.x := by linarith
    have hpowPos : 0 < Real.rpow S.x δ := Real.rpow_pos_of_pos hxpos δ
    have hHmPos : 0 < S.Hm := lt_of_lt_of_le hpowPos hHmLo
    have hHnPos : 0 < S.Hn := lt_of_lt_of_le hpowPos hHnLo
    have hYpos : 0 < S.Y := by
      unfold dyadicScales at hYmem
      rcases Finset.mem_filter.mp hYmem with ⟨hImage, _⟩
      rcases Finset.mem_image.mp hImage with ⟨k, _, hYeq⟩
      calc
        0 < (2 : ℝ) ^ k := pow_pos (by norm_num) k
        _ = S.Y := hYeq
    have hYge1 : 1 ≤ S.Y := by
      unfold dyadicScales at hYmem
      rcases Finset.mem_filter.mp hYmem with ⟨hImage, _⟩
      rcases Finset.mem_image.mp hImage with ⟨k, _, hYeq⟩
      rw [← hYeq]
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    have hDpos : 0 < (S.d₀ : ℝ) := by
      unfold padScales at hDmem
      rcases Finset.mem_image.mp hDmem with ⟨k, _, hDeq⟩
      rw [← hDeq]
      exact_mod_cast (pow_pos (by norm_num : 0 < (2 : ℕ)) k)
    have hDge1 : 1 ≤ (S.d₀ : ℝ) := by
      unfold padScales at hDmem
      rcases Finset.mem_image.mp hDmem with ⟨k, _, hDeq⟩
      rw [← hDeq]
      exact_mod_cast (one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2))
    have hHpos : 0 < S.H := by
      simpa [PDScale.H] using mul_pos hDpos hYpos
    have hHge1 : 1 ≤ S.H := by
      change 1 ≤ (S.d₀ : ℝ) * S.Y
      calc
        1 = 1 * 1 := by norm_num
        _ ≤ (S.d₀ : ℝ) * S.Y :=
          mul_le_mul hDge1 hYge1 (by norm_num) (by positivity)
    have hHmgt1 : 1 < S.Hm := by
      have hxgt1 : 1 < S.x := by linarith [hx₂]
      have hpowgt1 : 1 < Real.rpow S.x δ := Real.one_lt_rpow hxgt1 hδ
      exact lt_of_lt_of_le hpowgt1 hHmLo
    have hUlo : Real.rpow S.x δ ≤ S.U := by
      calc
        Real.rpow S.x δ ≤ S.Hm := hHmLo
        _ ≤ S.H * S.Hm := by
          calc
            S.Hm = 1 * S.Hm := by ring
            _ ≤ S.H * S.Hm := mul_le_mul_of_nonneg_right hHge1 hHmPos.le
        _ = S.U := by simp [PDScale.U]
    have hUpos : 0 < S.U := lt_of_lt_of_le hpowPos hUlo
    letI : Finite (PState F S) :=
      Finite.of_finite_univ (physicalState_finite hHpos hHmPos hHnPos)
    letI : Fintype (PState F S) := Fintype.ofFinite _
    have hStateFirst (P : PState F S) : 2 ≤ P.first := by
      have hfirstReal : 1 < (P.first : ℝ) := by
        have hproduct : 1 < S.H * S.Hm := by nlinarith
        exact lt_of_lt_of_le hproduct P.first_lower
      have hfirstNat : 1 < P.first := by exact_mod_cast hfirstReal
      omega
    have hStateRoot (P : PState F S) :
        stateRoot P = (rootC P.first P.second : ℝ) / (P.first : ℝ) :=
      stateRoot_eq_rootC_div P (hStateFirst P)
    have hEnvValidAll (P : PState F S) :
        EnvValid F S (P.pos, P.labels) := physicalState_envValid F S P
    have hLabelsValid (P : PState F S) :
        ValidPrimeLists S.x K F.a P.labels := by
      exact ⟨fun i j => ⟨P.label_prime i j, P.label_in_band i j⟩, P.label_distinct⟩
    have hLabelsSquarefree (P : PState F S) : Squarefree (groupLabelProduct P) := by
      simpa [groupLabelProduct] using
        primeListProduct_squarefree P.labels (hLabelsValid P) hBandsDisjoint
    have hLabelsRootRange (P : PState F S) :
        (groupLabelProduct P : ℝ) ≤
          Real.exp (4 * (K : ℝ) * Real.rpow S.L (21 / 100 : ℝ)) := by
      simpa [groupLabelProduct, PDScale.L] using
        primeListProduct_le_exp hBands P.labels (hLabelsValid P) hlogone
    have hRootLabelLines (P : PState F S) :
        ∀ q ∈ (groupLabelProduct P).primeFactors,
          kernelLine q P.first (rootC P.first P.second) = Fin.last q := by
      exact rootLines_last_of_list_divides P.labels (hLabelsValid P) P.first P.second
        (fun i j => P.label_divides i j)
    have hLabelModulusPos (P : PState F S) : 0 < groupLabelProduct P := by
      have hnat : 0 < groupLabelProduct P := by
        unfold groupLabelProduct
        apply Finset.prod_pos
        intro i hi
        apply Finset.prod_pos
        intro j hj
        exact (P.label_prime i j).pos
      exact hnat
    have hLogPowerGap : Real.rpow S.L (21 / 100 : ℝ) ≤
        Real.rpow S.L (98 / 100 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hlogone (by norm_num)
    have hLabelModulusRootRange (P : PState F S) :
        (groupLabelProduct P : ℝ) ≤
          Real.exp (CrootScale * Real.rpow S.L (98 / 100 : ℝ)) := by
      have hpower : 4 * (K : ℝ) * Real.rpow S.L (21 / 100 : ℝ) ≤
          CrootScale * Real.rpow S.L (98 / 100 : ℝ) := by
        dsimp [CrootScale]
        calc
          4 * (K : ℝ) * Real.rpow S.L (21 / 100 : ℝ) ≤
              4 * (K : ℝ) * Real.rpow S.L (98 / 100 : ℝ) :=
            mul_le_mul_of_nonneg_left hLogPowerGap (by positivity)
          _ ≤ (4 * (K : ℝ) + 1) * Real.rpow S.L (98 / 100 : ℝ) := by
            have hLnonneg : 0 ≤ S.L := by
              unfold PDScale.L
              linarith [hlogone]
            have hnonneg : 0 ≤ Real.rpow S.L (98 / 100 : ℝ) :=
              Real.rpow_nonneg hLnonneg _
            nlinarith
      exact (hLabelsRootRange P).trans (Real.exp_le_exp.mpr hpower)
    have hRootLineCount (P : PState F S) :=
      rootLines S.x hxRoot S.U S.Hn hUlo hHnLo (groupLabelProduct P)
        (hLabelsSquarefree P) (hLabelModulusPos P) (hLabelModulusRootRange P)
        (fun q => Fin.last q)
    have hPRootCoordinates (P : PState F S) :
        (1 ≤ (P.first : ℝ) / S.U ∧ (P.first : ℝ) / S.U ≤ 16) ∧
        (1 ≤ (P.second : ℝ) / S.Hn ∧ (P.second : ℝ) / S.Hn ≤ 2) ∧
        (0 ≤ (rootC P.first P.second : ℝ) / (P.first : ℝ) ∧
          (rootC P.first P.second : ℝ) / (P.first : ℝ) ≤ 1) := by
      have hfirstLo : S.U ≤ (P.first : ℝ) := by
        simpa [PDScale.U] using P.first_lower
      have hfirstHi : (P.first : ℝ) ≤ 16 * S.U := by
        calc
          (P.first : ℝ) ≤ 16 * S.H * S.Hm := P.first_upper
          _ = 16 * S.U := by simp [PDScale.U]; ring
      have hratioState : 0 ≤ stateRoot P ∧ stateRoot P ≤ 1 := by
        unfold stateRoot
        have hfirstPosNat : 0 < P.first :=
          lt_of_lt_of_le (by norm_num : 0 < 2) (hStateFirst P)
        have hfirstPos : 0 < (P.first : ℝ) := by exact_mod_cast hfirstPosNat
        constructor
        · exact div_nonneg (Int.cast_nonneg P.completion_range.1) hfirstPos.le
        · apply (div_le_iff₀ hfirstPos).2
          calc
            (P.completionC : ℝ) ≤ (P.first : ℝ) := by
              exact_mod_cast P.completion_range.2.le
            _ = 1 * (P.first : ℝ) := by ring
      have hratioRoot :
          0 ≤ (rootC P.first P.second : ℝ) / (P.first : ℝ) ∧
            (rootC P.first P.second : ℝ) / (P.first : ℝ) ≤ 1 := by
        rw [← hStateRoot P]
        exact hratioState
      refine ⟨⟨(le_div_iff₀ hUpos).2 (by simpa using hfirstLo),
          (div_le_iff₀ hUpos).2 hfirstHi⟩,
        ⟨(le_div_iff₀ hHnPos).2 (by simpa using P.second_lower),
          (div_le_iff₀ hHnPos).2 P.second_upper⟩,
        hratioRoot⟩
    have hPInRootLinesFullBox (P : PState F S) :
        (P.first, P.second) ∈
          {uv : ℕ × ℕ | Nat.Coprime uv.1 uv.2 ∧ 0 < uv.1 ∧
            1 ≤ (uv.1 : ℝ) / S.U ∧ (uv.1 : ℝ) / S.U ≤ 16 ∧
            1 ≤ (uv.2 : ℝ) / S.Hn ∧ (uv.2 : ℝ) / S.Hn ≤ 2 ∧
            0 ≤ (rootC uv.1 uv.2 : ℝ) / uv.1 ∧
            (rootC uv.1 uv.2 : ℝ) / uv.1 ≤ 1 ∧
            ∀ q ∈ (groupLabelProduct P).primeFactors,
              kernelLine q uv.1 (rootC uv.1 uv.2) = Fin.last q} := by
      simp only [Set.mem_setOf_eq]
      rcases hPRootCoordinates P with ⟨⟨h₁,h₂⟩,⟨h₃,h₄⟩,⟨h₅,h₆⟩⟩
      have hPpos : 0 < P.first := lt_of_lt_of_le (by norm_num : 0 < 2) (hStateFirst P)
      refine ⟨P.primitive, hPpos, h₁, h₂, h₃, h₄, h₅, h₆, ?_⟩
      exact hRootLabelLines P
    have hGoodExpansion := detPairing_goodExpansion F S family beta
    have hNoGoodExpansion := detPairing_noGoodExpansion F S family beta
    have hDifferenceExpansion := detPairing_difference_expansion F S family beta
    have hLpos : 0 < S.L := by
      unfold PDScale.L
      exact Real.log_pos (by linarith [hx₂])
    have hAlphaBound : ∀ m, family.alpha S.x m ≠ 0 →
        ‖family.alpha S.x m‖ ≤ Real.rpow S.L C := by
      intro m hm
      have hsupport := family.rough_support S.x hFamilyMin m hm
      simpa [PDScale.L] using family.coefficient_bound S.x hFamilyMin m hsupport.1
    have hBetaBound : ∀ n, beta n ≠ 0 → ‖beta n‖ ≤ Real.rpow S.L C := by
      rcases hbeta with ⟨hSupport, hBound⟩
      intro n hn
      have hnDyad := (hSupport n hn).1
      simpa [PDScale.L] using hBound n hnDyad
    have hEndpointFBound (P : PState F S) :
        ‖endpointF S.x K F.a family beta P‖ ≤ Real.rpow S.L (2 * C) := by
      by_cases hsq : Squarefree (groupLabelProduct P)
      · by_cases hα0 : family.alpha S.x (P.first / groupLabelProduct P) = 0
        · simp [endpointF, hsq, hα0]
          exact Real.rpow_nonneg hLpos.le _
        · by_cases hβ0 : beta P.second = 0
          · simp [endpointF, hsq, hβ0]
            exact Real.rpow_nonneg hLpos.le _
          · have hα := hAlphaBound _ hα0
            have hβ := hBetaBound _ hβ0
            have hpow : Real.rpow S.L C * Real.rpow S.L C =
                Real.rpow S.L (2 * C) := by
              calc
                Real.rpow S.L C * Real.rpow S.L C = Real.rpow S.L (C + C) :=
                  (Real.rpow_add hLpos C C).symm
                _ = Real.rpow S.L (2 * C) := by congr 1 <;> ring
            calc
              ‖endpointF S.x K F.a family beta P‖ =
                  ‖family.alpha S.x (P.first / groupLabelProduct P) *
                    star (beta P.second)‖ := by simp [endpointF, hsq]
              _ = ‖family.alpha S.x (P.first / groupLabelProduct P)‖ *
                    ‖star (beta P.second)‖ := norm_mul _ _
              _ = ‖family.alpha S.x (P.first / groupLabelProduct P)‖ *
                    ‖beta P.second‖ := by simp
              _ ≤ Real.rpow S.L C * Real.rpow S.L C :=
                    mul_le_mul hα hβ (norm_nonneg _) (Real.rpow_nonneg hLpos.le C)
              _ = Real.rpow S.L (2 * C) := hpow
      · simp [endpointF, hsq]
        exact Real.rpow_nonneg hLpos.le _
    have hEndpointGBound (P : PState F S) :
        ‖endpointG S.x K F.a family beta P‖ ≤ Real.rpow S.L (2 * C) := by
      by_cases hsq : Squarefree (groupLabelProduct P)
      · by_cases hα0 : family.alpha S.x (P.first / groupLabelProduct P) = 0
        · simp [endpointG, hsq, hα0]
          exact Real.rpow_nonneg hLpos.le _
        · by_cases hβ0 : beta P.second = 0
          · simp [endpointG, hsq, hβ0]
            exact Real.rpow_nonneg hLpos.le _
          · have hα := hAlphaBound _ hα0
            have hβ := hBetaBound _ hβ0
            have hpow : Real.rpow S.L C * Real.rpow S.L C =
                Real.rpow S.L (2 * C) := by
              calc
                Real.rpow S.L C * Real.rpow S.L C = Real.rpow S.L (C + C) :=
                  (Real.rpow_add hLpos C C).symm
                _ = Real.rpow S.L (2 * C) := by congr 1 <;> ring
            calc
              ‖endpointG S.x K F.a family beta P‖ =
                  ‖star (family.alpha S.x (P.first / groupLabelProduct P)) *
                    beta P.second‖ := by simp [endpointG, hsq]
              _ = ‖star (family.alpha S.x (P.first / groupLabelProduct P))‖ *
                    ‖beta P.second‖ := norm_mul _ _
              _ = ‖family.alpha S.x (P.first / groupLabelProduct P)‖ *
                    ‖beta P.second‖ := by simp
              _ ≤ Real.rpow S.L C * Real.rpow S.L C :=
                    mul_le_mul hα hβ (norm_nonneg _) (Real.rpow_nonneg hLpos.le C)
              _ = Real.rpow S.L (2 * C) := hpow
      · simp [endpointG, hsq]
        exact Real.rpow_nonneg hLpos.le _
    sorry
  · have hc₂' : c₂ ≤ 0 := le_of_not_gt hc₂
    refine ⟨1, 2, by norm_num, le_rfl, ?_⟩
    intro S hS hx family hFamilyAt hFamilyMin beta hbeta
    have hscale := family.scales family.xMin le_rfl
    have hxMin : 0 < family.xMin := lt_of_lt_of_le (by norm_num) family.xMin_ge_two
    have hleft : 0 < c₁ * family.xMin := mul_pos hc₁ hxMin
    have hright : c₂ * family.xMin ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc₂' hxMin.le
    have hprod : c₁ * family.xMin ≤ c₂ * family.xMin :=
      le_trans hscale.2.2.1 hscale.2.2.2
    exact False.elim ((not_le_of_gt hleft) (le_trans hprod hright))

/-- Extract the ordered shared slots of a valid prime list as a harmonic pad choice. -/
private def padChoiceFromLists {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (p : PrimeLists x K) (hp : ValidPrimeLists x K a p) : PadChoice x K a :=
  fun q => ⟨p q.1 (Fin.castSucc q.2), (hp.1 q.1 (Fin.castSucc q.2)).2⟩

/-- A slot transition has distinct pads that avoid both unshared endpoint labels. -/
private theorem padChoiceGood_of_slotTransition {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (p q : PrimeLists x K) (hp : ValidPrimeLists x K a p)
    (htrans : IsSlotTransition p q) :
    PadChoiceGood (padChoiceFromLists p hp) (fun i => q i (lastSlot x))
      (fun i => p i (lastSlot x)) := by
  constructor
  · intro addr
    constructor
    · intro heq
      exact (htrans.2 addr.1 addr.1 (Fin.castSucc addr.2)) heq.symm
    · intro heq
      have hlast : Fin.castSucc addr.2 ≠ lastSlot x := by
        intro h
        have hv := congrArg Fin.val h
        simp [lastSlot] at hv
        omega
      exact hp.2 addr.1 (Fin.castSucc addr.2) (lastSlot x) hlast heq
  · intro addr addr' hgroup haddr heq
    have hslot : Fin.castSucc addr.2 ≠ Fin.castSucc addr'.2 := by
      intro h
      have hval : addr.2.val = addr'.2.val := by simpa using congrArg Fin.val h
      exact haddr (Prod.ext hgroup (Fin.ext hval))
    apply hp.2 addr.1 (Fin.castSucc addr.2) (Fin.castSucc addr'.2) hslot
    simpa [padChoiceFromLists, hgroup] using heq

private theorem slot_eq_last_of_not_shared {x : ℝ}
    (j : Fin (slotCount x)) (hj : ¬ j.val < momentJ x) : j = lastSlot x := by
  apply Fin.ext
  have hjlt : j.val < momentJ x + 1 := by
    simpa [slotCount] using j.isLt
  have hjval : j.val = momentJ x := by omega
  simp [lastSlot, hjval]

private def padJoinLists {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (d : PadChoice x K a) (t : Fin K → ℕ) : PrimeLists x K :=
  fun i j => if h : j.val < momentJ x then (d (i, Fin.castLT j h)).val else t i

private def padJoinFunction {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (d : PadChoice x K a) (t : Fin K → ℕ) : Fin K → Fin (momentJ x + 1) → ℕ :=
  fun i j => if h : j.val < momentJ x then (d (i, Fin.castLT j h)).val else t i

private theorem padJoinLists_eq_padJoinFunction {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (d : PadChoice x K a) (t : Fin K → ℕ) (i : Fin K) (j : Fin (slotCount x)) :
    padJoinLists d t i j = padJoinFunction d t i j := rfl

private theorem padJoinLists_valid {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (d : PadChoice x K a) (t : Fin K → ℕ)
    (ht : ∀ i, t i ∈ primeBand x (a i))
    (hDistinct : ∀ i j j', j ≠ j' → (d (i, j)).val ≠ (d (i, j')).val)
    (hAvoid : ∀ i j, (d (i, j)).val ≠ t i) :
    ValidPrimeLists x K a (padJoinLists d t) := by
  unfold ValidPrimeLists
  constructor
  · intro i j
    by_cases hj : j.val < momentJ x
    · have hmem := (d (i, Fin.castLT j hj)).property
      have hprime := (Finset.mem_filter.mp hmem).2.1
      have hval : padJoinLists d t i j = (d (i, Fin.castLT j hj)).val := by
        simp [padJoinLists, hj]
      rw [hval]
      exact ⟨hprime, hmem⟩
    · have hjlast := slot_eq_last_of_not_shared j hj
      have hval : padJoinLists d t i j = t i := by
        rw [hjlast]
        simp [padJoinLists, lastSlot]
      rw [hval]
      exact ⟨(Finset.mem_filter.mp (ht i)).2.1, ht i⟩
  · intro i j j' hne
    by_cases hj : j.val < momentJ x
    · by_cases hj' : j'.val < momentJ x
      · have haddr : Fin.castLT j hj ≠ Fin.castLT j' hj' := by
          intro heq
          have hval : (Fin.castLT j hj).val = (Fin.castLT j' hj').val :=
            congrArg Fin.val heq
          have hval' : j.val = j'.val := by simpa using hval
          exact hne (Fin.ext hval')
        have hd := hDistinct i (Fin.castLT j hj) (Fin.castLT j' hj') haddr
        simpa [padJoinLists, hj, hj'] using hd
      · have hj'last := slot_eq_last_of_not_shared j' hj'
        have hleft : padJoinLists d t i j = (d (i, Fin.castLT j hj)).val := by
          simp [padJoinLists, hj]
        have hright : padJoinLists d t i j' = t i := by
          rw [hj'last]
          simp [padJoinLists, lastSlot]
        rw [hleft, hright]
        exact hAvoid i (Fin.castLT j hj)
    · have hjlast := slot_eq_last_of_not_shared j hj
      by_cases hj' : j'.val < momentJ x
      ·
        have hleft : padJoinLists d t i j = t i := by
          rw [hjlast]
          simp [padJoinLists, lastSlot]
        have hright : padJoinLists d t i j' = (d (i, Fin.castLT j' hj')).val := by
          simp only [padJoinLists, dif_pos hj']
        rw [hleft, hright]
        exact (hAvoid i (Fin.castLT j' hj')).symm
      · have hj'last := slot_eq_last_of_not_shared j' hj'
        exact (hne (hjlast.trans hj'last.symm)).elim

private theorem padJoinedLists_valid_of_good {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (d : PadChoice x K a) (ta tb : Fin K → ℕ)
    (hta : ∀ i, ta i ∈ primeBand x (a i)) (htb : ∀ i, tb i ∈ primeBand x (a i))
    (hgood : PadChoiceGood d ta tb) :
    ValidPrimeLists x K a (padJoinLists d ta) ∧
      ValidPrimeLists x K a (padJoinLists d tb) := by
  have hDistinct : ∀ i j j', j ≠ j' → (d (i, j)).val ≠ (d (i, j')).val := by
    intro i j j' hjj'
    apply hgood.2 (i, j) (i, j') rfl
    intro h
    exact hjj' (congrArg Prod.snd h)
  have hAvoidA : ∀ i j, (d (i, j)).val ≠ ta i := by
    intro i j
    exact (hgood.1 (i, j)).1
  have hAvoidB : ∀ i j, (d (i, j)).val ≠ tb i := by
    intro i j
    exact (hgood.1 (i, j)).2
  exact ⟨padJoinLists_valid d ta hta hDistinct hAvoidA,
    padJoinLists_valid d tb htb hDistinct hAvoidB⟩

private theorem padJoinedLists_slotTransition_of_good {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (d : PadChoice x K a) (ta tb : Fin K → ℕ)
    (hta : ∀ i, ta i ∈ primeBand x (a i)) (htb : ∀ i, tb i ∈ primeBand x (a i))
    (hgood : PadChoiceGood d ta tb)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand x (a i)) (primeBand x (a i')))
    (hCop : Nat.Coprime (tupleProduct ta) (tupleProduct tb)) :
    IsSlotTransition (padJoinLists d tb) (padJoinLists d ta) := by
  have htaDvd (i : Fin K) : ta i ∣ tupleProduct ta := by
    rw [tupleProduct]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have htbDvd (i : Fin K) : tb i ∣ tupleProduct tb := by
    rw [tupleProduct]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hnewDistinct (i : Fin K) : ta i ≠ tb i := by
    intro heq
    have htbDvdTa : ta i ∣ tupleProduct tb := by
      rw [heq]
      exact htbDvd i
    have hcommon : ta i ∣ Nat.gcd (tupleProduct ta) (tupleProduct tb) :=
      Nat.dvd_gcd (htaDvd i) htbDvdTa
    rw [hCop.gcd_eq_one] at hcommon
    exact (Finset.mem_filter.mp (hta i)).2.1.ne_one (Nat.dvd_one.mp hcommon)
  constructor
  · intro i j hj
    simp [padJoinLists, hj]
  · intro i i' j
    by_cases hj : j.val < momentJ x
    ·
      have htarget : padJoinLists d ta i (lastSlot x) = ta i := by
        simp [padJoinLists, lastSlot]
      have hsource : padJoinLists d tb i' j = (d (i', Fin.castLT j hj)).val := by
        simp [padJoinLists, hj]
      rw [htarget, hsource]
      by_cases hsame : i = i'
      · subst i'
        exact (hgood.1 (i, Fin.castLT j hj)).1.symm
      · have hneq : i' ≠ i := by
          intro heq
          exact hsame heq.symm
        have hnot : (d (i', Fin.castLT j hj)).val ∉ primeBand x (a i) :=
          (Finset.disjoint_left.mp (hBands i' i hneq))
            (d (i', Fin.castLT j hj)).property
        intro heq
        apply hnot
        rw [← heq]
        exact hta i
    · have hjlast := slot_eq_last_of_not_shared j hj
      have htarget : padJoinLists d ta i (lastSlot x) = ta i := by
        simp [padJoinLists, lastSlot]
      have hsource : padJoinLists d tb i' j = tb i' := by
        rw [hjlast]
        simp [padJoinLists, lastSlot]
      rw [htarget, hsource]
      by_cases hsame : i = i'
      · subst i'
        exact hnewDistinct i
      · have hneq : i' ≠ i := by
          intro heq
          exact hsame heq.symm
        have hnot : tb i' ∉ primeBand x (a i) :=
          (Finset.disjoint_left.mp (hBands i' i hneq)) (htb i')
        intro heq
        apply hnot
        rw [← heq]
        exact hta i

private theorem padJoinLists_lastProduct {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (d : PadChoice x K a) (t : Fin K → ℕ) :
    lastProduct (padJoinLists d t) = tupleProduct t := by
  classical
  unfold lastProduct tupleProduct
  apply Finset.prod_congr rfl
  intro i hi
  simp [padJoinLists, lastSlot]

private theorem padJoinLists_sharedProduct_inner {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (d : PadChoice x K a) (t : Fin K → ℕ) (i : Fin K) :
    (∏ j : Fin (momentJ x + 1),
      if j.val < momentJ x then padJoinFunction d t i j else 1) =
      ∏ j : Fin (momentJ x), (d (i, j)).val := by
  rw [Fin.prod_univ_castSucc]
  simp [padJoinFunction, lastSlot, Fin.castLT_castSucc]

private theorem padJoinLists_sharedProduct {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (d : PadChoice x K a) (t : Fin K → ℕ) :
    sharedProduct (padJoinLists d t) =
      ∏ i : Fin K, ∏ j : Fin (momentJ x), (d (i, j)).val := by
  classical
  unfold sharedProduct
  apply Finset.prod_congr rfl
  intro i hi
  change (∏ j : Fin (slotCount x),
      if j.val < momentJ x then padJoinLists d t i j else 1) = _
  simp_rw [padJoinLists_eq_padJoinFunction]
  change (∏ j : Fin (momentJ x + 1),
      if j.val < momentJ x then padJoinFunction d t i j else 1) = _
  exact padJoinLists_sharedProduct_inner d t i 

private theorem physicalMeasure_mul_freshNormalizer {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (hV : ∀ i : Fin K, 0 < bandMass x (a i)) :
    physicalMeasure x K a * (∏ i : Fin K, (bandMass x (a i))⁻¹) =
      ∏ i : Fin K, (bandMass x (a i))⁻¹ ^ (momentJ x + 2) := by
  classical
  unfold physicalMeasure
  rw [Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  let V := bandMass x (a i)
  have hVpos : 0 < V := hV i
  have hslot : slotCount x = momentJ x + 1 := rfl
  calc
    Real.rpow V (-(slotCount x : ℝ)) * V⁻¹ =
        V⁻¹ ^ slotCount x * V⁻¹ := by
      rw [Real.rpow_neg hVpos.le (slotCount x : ℝ), Real.rpow_natCast]
      simp [inv_pow, Real.rpow_natCast]
    _ = V⁻¹ ^ (momentJ x + 2) := by
      calc
        V⁻¹ ^ slotCount x * V⁻¹ = V⁻¹ ^ (slotCount x + 1) :=
          (pow_succ (V⁻¹) (slotCount x)).symm
        _ = V⁻¹ ^ (momentJ x + 2) := by simp [hslot]

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
  intro K F hF A hA
  by_cases hc₂ : 0 < c₂
  · have hBands : ValidBands K F.a := hF.1
    have hε : 0 < Real.log 2 / 2 := by positivity
    have hBandEvent : ∀ᶠ x : ℝ in atTop, ∀ i : Fin K,
        Real.log 2 / 2 ≤ bandMass x (F.a i) ∧ 0 < bandMass x (F.a i) := by
      rw [Filter.eventually_all]
      intro i
      have ha₀ : 0 < F.a i := lt_trans (by norm_num : (0 : ℝ) < 1 / 10)
        (hBands.2.1 i).1
      have ha₁ : F.a i < 1 := lt_trans (hBands.2.1 i).2
        (by norm_num : (1 / 5 : ℝ) < 1)
      obtain ⟨xBand, hxBand₂, hMass⟩ :=
        band_mass (F.a i) ha₀ ha₁ (Real.log 2 / 2) hε
      filter_upwards [Filter.eventually_ge_atTop xBand] with x hx
      refine ⟨?_, (hMass x hx).2⟩
      have habs := abs_le.mp (hMass x hx).1
      linarith
    obtain ⟨xBand, hBandEvent⟩ := Filter.eventually_atTop.mp hBandEvent
    obtain ⟨xDisjoint, hxDisjoint₂, bandsDisjoint⟩ :=
      validBands_disjoint_eventually K F.a hBands
    let x₀ : ℝ := max (Real.exp 1) (max 2 (max xBand xDisjoint))
    have hx₀₂ : 2 ≤ x₀ := by simp [x₀]
    have hx₀Band : xBand ≤ x₀ := by simp [x₀]
    have hx₀Disjoint : xDisjoint ≤ x₀ := by simp [x₀]
    have hx₀Exp : Real.exp 1 ≤ x₀ := by simp [x₀]
    refine ⟨1, x₀, by norm_num, hx₀₂, ?_⟩
    intro x hx family hfamilyMin beta hbeta Y hY
    have hxBand : xBand ≤ x := le_trans hx₀Band hx
    have hxDisjoint : xDisjoint ≤ x := le_trans hx₀Disjoint hx
    have hBandsDisjoint := bandsDisjoint x hxDisjoint
    have hBandMass : ∀ i, Real.log 2 / 2 ≤ bandMass x (F.a i) := fun i =>
      (hBandEvent x hxBand i).1
    have hBandMassPos : ∀ i, 0 < bandMass x (F.a i) := fun i =>
      (hBandEvent x hxBand i).2
    have hPadMass := padChoiceWeight_sum_eq_one F.a hBandMassPos
    have hPadChoiceTwoNormalizerFactor (d : PadChoice x K F.a) (t : Fin K → ℕ) :
        padChoiceWeight x F.a d *
            (∏ i : Fin K, (bandMass x (F.a i))⁻¹) ^ 2 =
          ((sharedProduct (padJoinLists d t) : ℝ)⁻¹) *
            ∏ i : Fin K, (bandMass x (F.a i))⁻¹ ^ (momentJ x + 2) := by
      rw [padChoiceWeight_group_two_normalizers]
      have hprod : padChoicePrimeProduct x d = sharedProduct (padJoinLists d t) := by
        rw [padJoinLists_sharedProduct]
        simp [padChoicePrimeProduct, Fintype.prod_prod_type]
      rw [hprod]
    have hxExp : Real.exp 1 ≤ x := le_trans hx₀Exp hx
    have hlog : 1 ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos 1) hxExp
      simpa using h
    have hVmin : 0 < Real.log 2 / 2 := by positivity
    have hAtomBound (q : Fin K × Fin (momentJ x))
        (p : {p : ℕ // p ∈ primeBand x (F.a q.1)}) :
        padAtomWeight x F.a q p ≤
          (Real.log 2 / 2)⁻¹ * Real.exp (-Real.rpow (Real.log x) (1 / 10 : ℝ)) := by
      have hpLower : Real.exp (Real.rpow (Real.log x) (1 / 10 : ℝ)) ≤ (p.val : ℝ) := by
        have haLow : (1 / 10 : ℝ) ≤ F.a q.1 := (hBands.2.1 q.1).1.le
        have hpow : Real.rpow (Real.log x) (1 / 10 : ℝ) ≤
            Real.rpow (Real.log x) (F.a q.1) :=
          Real.rpow_le_rpow_of_exponent_le hlog haLow
        exact le_trans (Real.exp_le_exp.mpr hpow)
          (Finset.mem_filter.mp p.property).2.2.1
      have hVinv : (bandMass x (F.a q.1))⁻¹ ≤ (Real.log 2 / 2)⁻¹ :=
        (inv_le_inv₀ (hBandMassPos q.1) hVmin).2 (hBandMass q.1)
      have hpPos : 0 < (p.val : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hpLower
      have hexpInv : (p.val : ℝ)⁻¹ ≤ Real.exp (-Real.rpow (Real.log x) (1 / 10 : ℝ)) := by
        rw [Real.exp_neg]
        exact (inv_le_inv₀ hpPos (Real.exp_pos _)).2 hpLower
      calc
        padAtomWeight x F.a q p =
            (bandMass x (F.a q.1))⁻¹ * (p.val : ℝ)⁻¹ := by
              simp [padAtomWeight, div_eq_mul_inv, mul_comm]
        _ ≤ (Real.log 2 / 2)⁻¹ *
            Real.exp (-Real.rpow (Real.log x) (1 / 10 : ℝ)) :=
              mul_le_mul hVinv hexpInv (by positivity) (by positivity)
    let εpad : ℝ := (Real.log 2 / 2)⁻¹ *
      Real.exp (-Real.rpow (Real.log x) (1 / 10 : ℝ))
    have hεpad : 0 ≤ εpad := by positivity
    have hPadPairCollision (q q' : Fin K × Fin (momentJ x)) (hqq' : q ≠ q') :
        (∑ d : PadChoice x K F.a,
          if (d q).val = (d q').val then padChoiceWeight x F.a d else 0) ≤ εpad := by
      exact padChoiceWeight_collision_mass_le_typed
        F.a hBandMassPos εpad hεpad hAtomBound q q' hqq'
    have hFixedLabelCollision (q : Fin K × Fin (momentJ x)) (t : ℕ)
        (ht : t ∈ primeBand x (F.a q.1)) :
        (∑ d : PadChoice x K F.a,
          if (d q).val = t then padChoiceWeight x F.a d else 0) ≤ εpad := by
      let tp : {p : ℕ // p ∈ primeBand x (F.a q.1)} := ⟨t, ht⟩
      have hconvert :
          (∑ d : PadChoice x K F.a,
            if (d q).val = t then padChoiceWeight x F.a d else 0) =
          (∑ d : PadChoice x K F.a,
            if d q = tp then padChoiceWeight x F.a d else 0) := by
        apply Finset.sum_congr rfl
        intro d hd
        by_cases h : (d q).val = t
        · have h' : d q = tp := Subtype.ext h
          simp [h, h', tp]
        · have h' : d q ≠ tp := by
            intro htEq
            exact h (congrArg Subtype.val htEq)
          simp [h, h', tp]
      calc
        _ = ∑ d : PadChoice x K F.a, if d q = tp then padChoiceWeight x F.a d else 0 := hconvert
        _ = padAtomWeight x F.a q tp := padChoiceWeight_coordinate_mass_typed F.a hBandMassPos q tp
        _ ≤ εpad := hAtomBound q tp
    have hForbiddenPadMass (ta tb : Fin K → ℕ)
        (hta : ∀ i, ta i ∈ primeBand x (F.a i))
        (htb : ∀ i, tb i ∈ primeBand x (F.a i)) :
        (∑ d ∈ padChoiceSet x F.a,
          if PadChoiceGood d ta tb then 0 else padChoiceWeight x F.a d) ≤
          (((2 * Fintype.card (Fin K × Fin (momentJ x)) +
            (padAddressPairs x K).card : ℕ) : ℝ) * εpad) := by
      apply padChoiceWeight_forbiddenMass_le F.a ta tb εpad hεpad hBandMassPos
      · intro q
        exact hFixedLabelCollision q (ta q.1) (hta q.1)
      · intro q
        exact hFixedLabelCollision q (tb q.1) (htb q.1)
      · intro q q' hgroup hne
        exact hPadPairCollision q q' hne
    have hJoinedValidAndTransition (d : PadChoice x K F.a) (ta tb : Fin K → ℕ)
        (hta : ∀ i, ta i ∈ primeBand x (F.a i))
        (htb : ∀ i, tb i ∈ primeBand x (F.a i))
        (hgood : PadChoiceGood d ta tb)
        (hcop : Nat.Coprime (tupleProduct ta) (tupleProduct tb)) :
        ((ValidPrimeLists x K F.a (padJoinLists d ta) ∧
          ValidPrimeLists x K F.a (padJoinLists d tb)) ∧
          IsSlotTransition (padJoinLists d tb) (padJoinLists d ta)) ∧
          sharedProduct (padJoinLists d tb) = sharedProduct (padJoinLists d ta) ∧
          lastProduct (padJoinLists d tb) = tupleProduct tb ∧
          lastProduct (padJoinLists d ta) = tupleProduct ta ∧
          padChoiceWeight x F.a d *
              (∏ i : Fin K, (bandMass x (F.a i))⁻¹) ^ 2 =
            (sharedProduct (padJoinLists d ta) : ℝ)⁻¹ *
              ∏ i : Fin K, (bandMass x (F.a i))⁻¹ ^ (momentJ x + 2) := by
      refine ⟨⟨padJoinedLists_valid_of_good d ta tb hta htb hgood,
        padJoinedLists_slotTransition_of_good d ta tb hta htb hgood hBandsDisjoint hcop⟩,
        ?_, padJoinLists_lastProduct d tb, padJoinLists_lastProduct d ta,
        hPadChoiceTwoNormalizerFactor d ta⟩
      rw [padJoinLists_sharedProduct, padJoinLists_sharedProduct]
    sorry
  · have hc₂' : c₂ ≤ 0 := le_of_not_gt hc₂
    refine ⟨1, 2, by norm_num, le_rfl, ?_⟩
    intro x hx family hfamilyMin beta hbeta Y hY
    have hscale := family.scales family.xMin le_rfl
    have hxMin : 0 < family.xMin := lt_of_lt_of_le (by norm_num) family.xMin_ge_two
    have hleft : 0 < c₁ * family.xMin := mul_pos hc₁ hxMin
    have hright : c₂ * family.xMin ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc₂' hxMin.le
    have hprod : c₁ * family.xMin ≤ c₂ * family.xMin :=
      le_trans hscale.2.2.1 hscale.2.2.2
    exact False.elim ((not_le_of_gt hleft) (le_trans hprod hright))

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
  · have hc₂' : c₂ ≤ 0 := le_of_not_gt hc₂
    refine ⟨1, 2, by norm_num, le_rfl, ?_⟩
    intro x hx₀ family hfamilyMin beta hbeta Y hY E₀ Ce Cp hPairs
    have hscale := family.scales family.xMin le_rfl
    have hxMin : 0 < family.xMin := lt_of_lt_of_le (by norm_num) family.xMin_ge_two
    have hleft : 0 < c₁ * family.xMin := mul_pos hc₁ hxMin
    have hright : c₂ * family.xMin ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc₂' hxMin.le
    have hprod : c₁ * family.xMin ≤ c₂ * family.xMin :=
      le_trans hscale.2.2.1 hscale.2.2.2
    exact False.elim ((not_le_of_gt hleft) (le_trans hprod hright))

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
