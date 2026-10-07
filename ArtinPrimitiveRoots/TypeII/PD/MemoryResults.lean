import ArtinPrimitiveRoots.TypeII.PD.Memory
import ArtinPrimitiveRoots.TypeII.PD.Determinant
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
(mem:edge-crude; columns via the adjoint rules, PD 04:310-348). -/
theorem ghost_edge_crude (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ v₀ C_K Cexp x₀ : ℝ, 1 < v₀ ∧ 0 < C_K ∧ 0 < Cexp ∧ 2 ≤ x₀ ∧
        ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
          ∀ w : ArchRoot, w.InRegion S → ∀ j : ℕ, j ≤ S.N →
            MemRowSchurLE F S (memoryCutoff S) (memGhost F S ρ j) v₀ C_K ∧
            MemColSchurLE F S (memoryCutoff S) (memGhost F S ρ j) v₀ C_K ∧
            MemOpNormLE F S (memoryCutoff S) (memGhost F S ρ j) C_K ∧
            (j < S.N →
              MemRowSchurLE F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.full j) v₀
                (Real.rpow S.L Cexp) ∧
              MemColSchurLE F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.full j) v₀
                (Real.rpow S.L Cexp)) := by
  sorry

/-- `t2:pd.lattice-clean` (a) — PD 04:439-497.  Lattice box at a source passing good test (i):
in the coordinates `(h,l)` of `z' = h z + l D w_z`, the region `|l| ≤ C₁ Y`, `|h + lα| ≤ C₁`
(`α = D τ(w_z)/τ(z)`, from cell separation and the box) is covered, after a unimodular change of
coordinates, by a centered box with sides `A', B'`, `A'B' ≪ Y`, `Y^{0.1} ≤ A',B' ≤ Y^{0.9}`
(mem:lattice-shape).  Pure geometry of numbers: shortest vector `≥ Y^{-0.8}` by test (i),
`≪ Y^{-1/2}` by Dirichlet. -/
theorem lattice_shape (C₁ : ℝ) (hC₁ : 1 ≤ C₁) :
    ∃ C₂ Y₀ : ℝ, 0 < C₂ ∧ 1 ≤ Y₀ ∧ ∀ Y : ℝ, Y₀ ≤ Y → ∀ α : ℝ,
      (∀ l : ℕ, 1 ≤ l → (l : ℝ) ≤ Real.rpow Y (1 / 5 : ℝ) →
        Real.rpow Y (-(7 / 10 : ℝ)) < circleDistance ((l : ℝ) * α)) →
      ∃ (a₀ b₀ c₀ d₀ : ℤ) (A' B' : ℝ), a₀ * d₀ - b₀ * c₀ = 1 ∧ A' * B' ≤ C₂ * Y ∧
        Real.rpow Y (1 / 10 : ℝ) ≤ A' ∧ A' ≤ Real.rpow Y (9 / 10 : ℝ) ∧
        Real.rpow Y (1 / 10 : ℝ) ≤ B' ∧ B' ≤ Real.rpow Y (9 / 10 : ℝ) ∧
        ∀ h l : ℤ, |(l : ℝ)| ≤ C₁ * Y → |(h : ℝ) + (l : ℝ) * α| ≤ C₁ →
          |((d₀ * h - b₀ * l : ℤ) : ℝ)| ≤ A' ∧ |((a₀ * l - c₀ * h : ℤ) : ℝ)| ≤ B' := by
  sorry

/-- `t2:pd.lattice-clean` (b) — PD 04:499-603.  REPLACES the frozen `lattice_clean`.  For every
`G` there is `A₀` with `‖ℰ_j^{clean}‖_{ℋ_B} ≤ L^{-G}` (mem:clean-bound): condition on shared list
and memory, drop the extra ban (cost `C_K M sup ν`), reduce by `lattice_shape` to the
determinant-exponential matrix on the box (mem:clean-kernel), Fourier-diagonalize the product
variable, Dirichlet approximation on `𝕋 ∖ 𝔐` (mem:dirichlet-minor) and the Gram bound
(mem:bilinear-gram) give `L^{0.2-A₀} + Y^{-0.1} log Y`; `A₀` independent of `K`. -/
theorem lattice_clean (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) (q_d : ℝ) (eta psi : ℝ → ℝ) :
    ∀ G : ℝ, 0 < G → ∃ A₀ : ℝ, 0 < A₀ ∧
      ∀ (K : ℕ) (F : PDFix K), F.Valid → F.Has q_d A₀ eta psi →
        ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
          ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
            ∀ w : ArchRoot, w.InRegion S → ∀ j : ℕ, j < S.N →
              MemOpNormLE F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.clean j)
                (Real.rpow S.L (-G)) := by
  sorry

/-- `t2:pd.dirty-raw` — PD 04:605-714.  REPLACES the frozen `dirty_raw`.  With
`ε_K = C_K(B/M_J^K + B^K e^{-cL^{0.1}})`: every raw piece with `(St,Pr) ≠ (∅,∅)` has weighted row
sum `≤ ε_K` if `Pr ≠ ∅` (one compatible omission tuple by test (ii), mass `M_J^{-K}`,
(mem:anchor-congruence)) and `≤ C_K` otherwise, column sum `≤ ε_K` if `St ≠ ∅` and `≤ C_K`
otherwise (reversal); weighted Schur gives `‖dirty raw‖ ≤ C_K √ε_K ≤ C_K L^{1-K/200}` for large
`x` (mem:raw-dirty-norm).  Stated for `K ≥ 201`, where `ε_K ≤ 1` eventually. -/
theorem dirty_raw (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ), 201 ≤ K → ∀ (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ v₀ C_K c x₀ : ℝ, 1 < v₀ ∧ 0 < C_K ∧ 0 < c ∧ 2 ≤ x₀ ∧
        ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
          ∀ w : ArchRoot, w.InRegion S → ∀ j : ℕ, j < S.N →
            let B := memoryCutoff S
            let εK := C_K * ((B : ℝ) / (S.M : ℝ) ^ K +
              (B : ℝ) ^ K * Real.exp (-c * Real.rpow S.L (1 / 10 : ℝ)))
            (∀ St Pr : Finset (Fin K), ¬ (St = ∅ ∧ Pr = ∅) →
              MemRowSchurLE F S B (memEdgePiece F S ρ w true St Pr j) v₀
                  (if Pr.Nonempty then εK else C_K) ∧
                MemColSchurLE F S B (memEdgePiece F S ρ w true St Pr j) v₀
                  (if St.Nonempty then εK else C_K)) ∧
            MemOpNormLE F S B (memEdge F S ρ w EdgeKind.dirtyRaw j)
              (C_K * Real.rpow S.L (1 - (K : ℝ) / 200)) := by
  sorry

/-- `t2:pd.dirty-comparison` — PD 04:716-770.  REPLACES the frozen `dirty_comparison`.
Comparison pieces with `(St,Pr) ≠ (∅,∅)`: a promoted index needs one prescribed line at the
target, one nonzero linear congruence in the lattice box (mem:line-count), row sum
`ζ_K = C_K L^{3A₀} B^K (p_min^{-1} + Y^{-0.1}) = O_A(L^{-A})`; the opposite side is `≤ L^C`
(mem:edge-crude); weighted Schur gives every fixed negative power of `L`. -/
theorem dirty_comparison (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ → ∀ A : ℝ, 0 < A →
      ∃ C_A x₀ : ℝ, 0 < C_A ∧ 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S → ∀ j : ℕ, j < S.N →
          MemOpNormLE F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.dirtyCmp j)
            (C_A * Real.rpow S.L (-A)) := by
  sorry

/-- `t2:pd.signed-edge` (new assembly node) — PD 04:772-782 (mem:signed-edge).  Choose `A₀`
from `lattice_clean` for `G+1`, then `K₀` with `K₀/200 > G+2`: `‖ℰ_j‖_{ℋ_B} ≤ L^{-G}`
(`ℰ_j = clean + dirtyRaw - dirtyCmp` by definition). -/
theorem signed_edge (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) (q_d : ℝ) (eta psi : ℝ → ℝ) :
    ∀ G : ℝ, 0 < G → ∃ A₀ : ℝ, 0 < A₀ ∧ ∃ K₀ : ℕ,
      ∀ (K : ℕ), K₀ ≤ K → ∀ (F : PDFix K), F.Valid → F.Has q_d A₀ eta psi →
        ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
          ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
            ∀ w : ArchRoot, w.InRegion S → ∀ j : ℕ, j < S.N →
              MemOpNormLE F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.full j)
                (Real.rpow S.L (-G)) := by
  sorry

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
`ghost_edge_crude` and `‖𝐛‖² ≤ 2` (mem:boundary-norm). -/
theorem history_rank_low (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ C_K Ccr x₀ : ℝ, 0 < C_K ∧ 0 < Ccr ∧ 2 ≤ x₀ ∧
        ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x → ∀ w : ArchRoot, w.InRegion S →
          ∀ G : ℝ, 0 < G →
            (∀ j : ℕ, j < S.N →
              MemOpNormLE F S (memoryCutoff S) (memEdge F S ρ w EdgeKind.full j)
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
        ∀ family : CoefficientFamily δ C c₁ c₂, ∀ beta : ℕ → ℂ,
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
        ∀ family : CoefficientFamily δ C c₁ c₂, ∀ beta : ℕ → ℂ,
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
  sorry

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
  sorry

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
  sorry


end

end ArtinPrimitiveRoots.TypeII.PD
