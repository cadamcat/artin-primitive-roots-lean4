import ArtinPrimitiveRoots.TypeII.Proofs.«PD-HIGH».Defs
import Mathlib.Data.Finset.Sort

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.unusedVariables false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
open ArtinPrimitiveRoots.TypeII
noncomputable section

/-- Triangular finite atom bound with arbitrary finite coordinates. A forced coordinate `k`
must have value `val k (b k)` equal to an instruction reading only the values of strictly
earlier coordinates; the fibre of every such instruction has mass at most `Δ`. -/
theorem pcr_triangular_general (n : ℕ) (X : Fin n → Type*) [∀ k, Fintype (X k)]
    (val : (k : Fin n) → X k → ℕ) (ν : (k : Fin n) → X k → ℝ)
    (R : Finset (Fin n)) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (pick : (k : Fin n) → (Fin k.val → ℕ) → ℕ)
    (hν : ∀ k x, 0 ≤ ν k x)
    (hatom : ∀ k ∈ R, ∀ pre : Fin k.val → ℕ,
      (∑ x : X k, if val k x = pick k pre then ν k x else 0) ≤ Δ) :
    (∑ b : (k : Fin n) → X k,
      if ∀ k ∈ R, val k (b k) = pick k
        (fun j => val ⟨j.val, lt_trans j.isLt k.isLt⟩ (b ⟨j.val, lt_trans j.isLt k.isLt⟩))
      then ∏ k : Fin n, ν k (b k) else 0) ≤
      ∏ k : Fin n, if k ∈ R then Δ else ∑ x : X k, ν k x := by
  induction n generalizing Δ with
  | zero => simp
  | succ n ih =>
    let R₀ : Finset (Fin n) := Finset.univ.filter fun k => k.castSucc ∈ R
    let X₀ : Fin n → Type _ := fun k => X k.castSucc
    let val₀ : (k : Fin n) → X₀ k → ℕ := fun k => val k.castSucc
    let ν₀ : (k : Fin n) → X₀ k → ℝ := fun k => ν k.castSucc
    let pick₀ : (k : Fin n) → (Fin k.val → ℕ) → ℕ := fun k => pick k.castSucc
    let good₀ (b : (k : Fin n) → X₀ k) : Prop :=
      ∀ k ∈ R₀, val₀ k (b k) = pick₀ k
        (fun j => val₀ ⟨j.val, lt_trans j.isLt k.isLt⟩ (b ⟨j.val, lt_trans j.isLt k.isLt⟩))
    let wt₀ (b : (k : Fin n) → X₀ k) : ℝ :=
      if good₀ b then ∏ k : Fin n, ν₀ k (b k) else 0
    let c : ℝ := if Fin.last n ∈ R then Δ else ∑ x : X (Fin.last n), ν (Fin.last n) x
    have hc : 0 ≤ c := by
      dsimp [c]
      split_ifs
      · exact hΔ
      · exact Finset.sum_nonneg fun x _ => hν _ x
    have hw₀ (b : (k : Fin n) → X₀ k) : 0 ≤ wt₀ b := by
      dsimp [wt₀]
      split_ifs
      · exact Finset.prod_nonneg fun k _ => hν _ _
      · exact le_rfl
    let wt (b : (k : Fin (n + 1)) → X k) : ℝ :=
      if ∀ k ∈ R, val k (b k) = pick k
        (fun j => val ⟨j.val, lt_trans j.isLt k.isLt⟩ (b ⟨j.val, lt_trans j.isLt k.isLt⟩))
      then ∏ k : Fin (n + 1), ν k (b k) else 0
    have hvalue (b : (k : Fin n) → X₀ k) (p : X (Fin.last n)) :
        (fun k => val k ((Fin.snoc (α := X) b p) k)) =
          Fin.snoc (α := fun _ => ℕ) (fun k => val₀ k (b k)) (val (Fin.last n) p) := by
      funext k
      refine Fin.lastCases ?_ (fun k => ?_) k <;> simp [val₀]
    have hgood (b : (k : Fin n) → X₀ k) (p : X (Fin.last n)) :
        (∀ k ∈ R, val k ((Fin.snoc (α := X) b p) k) = pick k
          (fun j => val ⟨j.val, lt_trans j.isLt k.isLt⟩
            ((Fin.snoc (α := X) b p) ⟨j.val, lt_trans j.isLt k.isLt⟩))) ↔
          good₀ b ∧ (Fin.last n ∈ R →
            val (Fin.last n) p = pick (Fin.last n) (fun j => val₀ j (b j))) := by
      have hv (k : Fin (n + 1)) := congrFun (hvalue b p) k
      simp_rw [hv]
      constructor
      · intro h
        constructor
        · intro k hk
          have he := h k.castSucc (Finset.mem_filter.mp hk).2
          simp only [Fin.snoc_castSucc] at he
          calc
            val₀ k (b k) = pick k.castSucc
                (fun j => Fin.snoc (α := fun _ => ℕ) (fun k => val₀ k (b k)) (val (Fin.last n) p)
                  ⟨j.val, lt_trans j.isLt k.castSucc.isLt⟩) := he
            _ = pick₀ k (fun j => val₀ ⟨j.val, lt_trans j.isLt k.isLt⟩
                  (b ⟨j.val, lt_trans j.isLt k.isLt⟩)) := by
              apply congrArg (pick k.castSucc)
              funext j
              exact Fin.snoc_castSucc (α := fun _ => ℕ) (val (Fin.last n) p)
                (fun k => val₀ k (b k)) ⟨j.val, lt_trans j.isLt k.isLt⟩
        · intro hk
          have he := h (Fin.last n) hk
          simp only [Fin.snoc_last] at he
          calc
            val (Fin.last n) p = pick (Fin.last n)
                (fun j => Fin.snoc (α := fun _ => ℕ) (fun k => val₀ k (b k)) (val (Fin.last n) p)
                  ⟨j.val, lt_trans j.isLt (Fin.last n).isLt⟩) := he
            _ = pick (Fin.last n) (fun j => val₀ j (b j)) := by
              apply congrArg (pick (Fin.last n))
              funext j
              exact Fin.snoc_castSucc (α := fun _ => ℕ) (val (Fin.last n) p)
                (fun k => val₀ k (b k)) j
      · rintro ⟨h₀, hl⟩ k hk
        by_cases hkl : k = Fin.last n
        · subst k
          simp only [Fin.snoc_last]
          calc
            val (Fin.last n) p = pick (Fin.last n) (fun j => val₀ j (b j)) := hl hk
            _ = pick (Fin.last n)
                (fun j => Fin.snoc (α := fun _ => ℕ) (fun k => val₀ k (b k)) (val (Fin.last n) p)
                  ⟨j.val, lt_trans j.isLt (Fin.last n).isLt⟩) := by
              apply congrArg (pick (Fin.last n))
              funext j
              exact (Fin.snoc_castSucc (α := fun _ => ℕ) (val (Fin.last n) p)
                (fun k => val₀ k (b k)) j).symm
        · obtain ⟨k₀, rfl⟩ := Fin.exists_castSucc_eq.mpr hkl
          simp only [Fin.snoc_castSucc]
          have hk₀ : k₀ ∈ R₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
          calc
            val₀ k₀ (b k₀) = pick₀ k₀
                (fun j => val₀ ⟨j.val, lt_trans j.isLt k₀.isLt⟩
                  (b ⟨j.val, lt_trans j.isLt k₀.isLt⟩)) := h₀ k₀ hk₀
            _ = pick k₀.castSucc
                (fun j => Fin.snoc (α := fun _ => ℕ) (fun k => val₀ k (b k)) (val (Fin.last n) p)
                  ⟨j.val, lt_trans j.isLt k₀.castSucc.isLt⟩) := by
              apply congrArg (pick k₀.castSucc)
              funext j
              exact (Fin.snoc_castSucc (α := fun _ => ℕ) (val (Fin.last n) p)
                (fun k => val₀ k (b k)) ⟨j.val, lt_trans j.isLt k₀.isLt⟩).symm
    have hsplit (b : (k : Fin n) → X₀ k) (p : X (Fin.last n)) :
        wt ((Fin.snoc (α := X) b p)) = wt₀ b *
          (if Fin.last n ∈ R then
            if val (Fin.last n) p = pick (Fin.last n) (fun j => val₀ j (b j))
            then ν (Fin.last n) p else 0
          else ν (Fin.last n) p) := by
      dsimp only [wt, wt₀]
      rw [ite_cond_congr (propext (hgood b p))]
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      by_cases hb : good₀ b <;> by_cases hl : Fin.last n ∈ R <;>
        by_cases hp : val (Fin.last n) p = pick (Fin.last n) (fun j => val₀ j (b j)) <;>
        simp [hb, hl, hp, ν₀]
    have hlocal (b : (k : Fin n) → X₀ k) :
        (∑ p : X (Fin.last n), wt ((Fin.snoc (α := X) b p))) ≤ wt₀ b * c := by
      simp_rw [hsplit]
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ (hw₀ b)
      by_cases hl : Fin.last n ∈ R
      · simp only [hl, if_true, c]
        exact hatom (Fin.last n) hl (fun j => val₀ j (b j))
      · simp only [hl, if_false, c]
        exact le_rfl
    have hih := ih X₀ val₀ ν₀ R₀ Δ hΔ pick₀
      (fun k x => hν k.castSucc x)
      (fun k hk pre => hatom k.castSucc (Finset.mem_filter.mp hk).2 pre)
    calc
      _ = ∑ p : X (Fin.last n), ∑ b : (k : Fin n) → X₀ k,
            wt ((Fin.snoc (α := X) b p)) := by
        rw [← (Fin.snocEquiv X).sum_comp wt, Fintype.sum_prod_type]
        rfl
      _ = ∑ b : (k : Fin n) → X₀ k, ∑ p : X (Fin.last n),
            wt ((Fin.snoc (α := X) b p)) :=
        Finset.sum_comm
      _ ≤ ∑ b : (k : Fin n) → X₀ k, wt₀ b * c :=
        Finset.sum_le_sum fun b _ => hlocal b
      _ = (∑ b : (k : Fin n) → X₀ k, wt₀ b) * c := by rw [Finset.sum_mul]
      _ ≤ (∏ k : Fin n, if k ∈ R₀ then Δ else ∑ x : X₀ k, ν₀ k x) * c :=
        mul_le_mul_of_nonneg_right hih hc
      _ = _ := by
        rw [Fin.prod_univ_castSucc]
        simp [R₀, X₀, ν₀, c]

theorem pcr_coordinate_fibre (P : Finset ℕ) (ν : ℕ → ℝ)
    (pick : ℕ) (Δ : ℝ) (hΔ : 0 ≤ Δ) (ha : ∀ p ∈ P, ν p ≤ Δ) :
    (∑ p : P, if (p : ℕ) = pick then ν p else 0) ≤ Δ := by
  by_cases hp : pick ∈ P
  · let p₀ : P := ⟨pick, hp⟩
    rw [Finset.sum_eq_single p₀]
    · simpa [p₀] using ha pick hp
    · intro p _ hne
      have hv : (p : ℕ) ≠ pick := fun he => hne (Subtype.ext he)
      simp [hv]
    · simp
  · have hz : (∑ p : P, if (p : ℕ) = pick then ν p else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro p _
      have hv : (p : ℕ) ≠ pick := fun he => hp (he ▸ p.property)
      simp [hv]
    rw [hz]
    exact hΔ

/-- The prefix-dependent triangular bound on finite sets of naturals (the statement of
the frozen `pd5_triangular_birth_sum_le`), derived from the general version. -/
theorem pcr_triangular_nat (n : ℕ) (P : Fin n → Finset ℕ)
    (ν : Fin n → ℕ → ℝ) (R : Finset (Fin n)) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (pick : (k : Fin n) → (Fin k.val → ℕ) → ℕ)
    (hν : ∀ k p, p ∈ P k → 0 ≤ ν k p)
    (hatom : ∀ k ∈ R, ∀ p ∈ P k, ν k p ≤ Δ) :
    (∑ b : (k : Fin n) → {p : ℕ // p ∈ P k},
      if ∀ k ∈ R, (b k : ℕ) = pick k
        (fun j => (b ⟨j.val, lt_trans j.isLt k.isLt⟩ : ℕ))
      then ∏ k : Fin n, ν k (b k) else 0) ≤
      ∏ k : Fin n, if k ∈ R then Δ else ∑ p ∈ P k, ν k p := by
  have h := pcr_triangular_general n (fun k => {p : ℕ // p ∈ P k}) (fun k x => (x : ℕ))
    (fun k x => ν k x) R Δ hΔ pick (fun k x => hν k x x.property)
    (fun k hk pre => pcr_coordinate_fibre (P k) (ν k) (pick k pre) Δ hΔ (hatom k hk))
  refine h.trans (le_of_eq ?_)
  apply Finset.prod_congr rfl
  intro k _
  split_ifs
  · rfl
  · exact Finset.sum_coe_sort (P k) (ν k)

/-- The triangular atom bound on any finite ordered coordinate set. -/
theorem pcr_ordered_triangular_birth_sum_le {α : Type*} [Fintype α] [LinearOrder α]
    (P : α → Finset ℕ) (ν : α → ℕ → ℝ) (R : Finset α) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (pick : (a : α) → ({b : α // b < a} → ℕ) → ℕ)
    (hν : ∀ a p, p ∈ P a → 0 ≤ ν a p)
    (hatom : ∀ a ∈ R, ∀ p ∈ P a, ν a p ≤ Δ) :
    (∑ b : (a : α) → {p : ℕ // p ∈ P a},
      if ∀ a ∈ R, (b a : ℕ) = pick a (fun z => (b z.1 : ℕ))
      then ∏ a : α, ν a (b a) else 0) ≤
      ∏ a : α, if a ∈ R then Δ else ∑ p ∈ P a, ν a p := by
  let n := Fintype.card α
  let e : Fin n ≃o α := Fintype.orderIsoFinOfCardEq α rfl
  let ep := Equiv.piCongrLeft (fun a : α => {p : ℕ // p ∈ P a}) e.toEquiv
  let R₀ : Finset (Fin n) := Finset.univ.filter fun k => e k ∈ R
  let pick₀ (k : Fin n) (pastValues : Fin k.val → ℕ) : ℕ :=
    pick (e k) (fun z => pastValues ⟨(e.symm z.1).val, by
      have hi : e.symm z.1 < k := by simpa using e.symm.strictMono z.2
      exact hi⟩)
  have happ (c : (k : Fin n) → {p : ℕ // p ∈ P (e k)}) (k : Fin n) :
      (ep c) (e k) = c k :=
    Equiv.piCongrLeft_apply_apply (P := fun a : α => {p : ℕ // p ∈ P a}) (e := e.toEquiv) c k
  have hsym (k : Fin n) : e.symm (e k) = k := e.symm_apply_apply k
  have hpick (c : (k : Fin n) → {p : ℕ // p ∈ P (e k)}) (k : Fin n) :
      pick₀ k (fun j => (c ⟨j.val, lt_trans j.isLt k.isLt⟩ : ℕ)) =
        pick (e k) (fun z => ((ep c) z.1 : ℕ)) := by
    apply congrArg (pick (e k))
    funext z
    rcases z with ⟨a, ha⟩
    obtain ⟨i, rfl⟩ := e.surjective a
    change (c (e.symm (e i)) : ℕ) = ((ep c) (e i) : ℕ)
    rw [hsym, happ]
  have hpred (c : (k : Fin n) → {p : ℕ // p ∈ P (e k)}) :
      (∀ a ∈ R, ((ep c) a : ℕ) = pick a (fun z => ((ep c) z.1 : ℕ))) ↔
      (∀ k ∈ R₀, (c k : ℕ) = pick₀ k
        (fun j => (c ⟨j.val, lt_trans j.isLt k.isLt⟩ : ℕ))) := by
    constructor
    · intro h k hk
      have he := h (e k) (Finset.mem_filter.mp hk).2
      rw [hpick]
      simpa only [happ] using he
    · intro h a ha
      obtain ⟨k, rfl⟩ := e.surjective a
      have hk : k ∈ R₀ := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
      simpa only [happ, hpick] using h k hk
  let wt (b : (a : α) → {p : ℕ // p ∈ P a}) : ℝ :=
    if ∀ a ∈ R, (b a : ℕ) = pick a (fun z => (b z.1 : ℕ))
    then ∏ a : α, ν a (b a) else 0
  have hterm (c : (k : Fin n) → {p : ℕ // p ∈ P (e k)}) :
      wt (ep c) = if ∀ k ∈ R₀, (c k : ℕ) = pick₀ k
        (fun j => (c ⟨j.val, lt_trans j.isLt k.isLt⟩ : ℕ))
        then ∏ k : Fin n, ν (e k) (c k) else 0 := by
    dsimp only [wt]
    rw [ite_cond_congr (propext (hpred c))]
    congr 1
    have he := e.toEquiv.prod_comp (fun a => ν a ((ep c) a))
    change (∏ k : Fin n, ν (e k) ((ep c) (e k))) =
      ∏ a : α, ν a ((ep c) a) at he
    simp only [happ] at he
    exact he.symm
  have h := pcr_triangular_nat n (fun k => P (e k)) (fun k => ν (e k)) R₀ Δ hΔ
    pick₀ (fun k p hp => hν (e k) p hp)
    (fun k hk p hp => hatom (e k) (Finset.mem_filter.mp hk).2 p hp)
  calc
    _ = ∑ c : (k : Fin n) → {p : ℕ // p ∈ P (e k)}, wt (ep c) := by
      exact (ep.sum_comp wt).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      exact hterm c
    _ ≤ ∏ k : Fin n, if k ∈ R₀ then Δ else ∑ p ∈ P (e k), ν (e k) p := h
    _ = _ := by
      have he := e.toEquiv.prod_comp (fun a => if a ∈ R then Δ else ∑ p ∈ P a, ν a p)
      simpa [R₀] using he

noncomputable def pcr_coordinateLog {α : Type*} {K : ℕ} (L : List α)
    (address : α → BirthAddress K) (values : α → ℕ) : BirthLog K :=
  L.map fun a => (address a, values a)

theorem pcr_coordinateLog_filter_congr {α : Type*} {K : ℕ}
    (S : PDScale) (B : ℕ) (L : List α) (address : α → BirthAddress K)
    (p q : α → ℕ) (a : BirthAddress K)
    (hpq : ∀ z ∈ L, pd5_birthIndex S B (address z) < pd5_birthIndex S B a → p z = q z) :
    (pcr_coordinateLog L address p).filter
        (fun e => pd5_birthIndex S B e.1 < pd5_birthIndex S B a) =
      (pcr_coordinateLog L address q).filter
        (fun e => pd5_birthIndex S B e.1 < pd5_birthIndex S B a) := by
  unfold pcr_coordinateLog
  rw [List.filter_map, List.filter_map]
  apply List.map_congr_left
  intro z hz
  have h : z ∈ L ∧ pd5_birthIndex S B (address z) < pd5_birthIndex S B a := by
    simpa using List.mem_filter.mp hz
  simp [hpq z h.1 h.2]

theorem pcr_coordinateLog_label {α : Type*} {K : ℕ} (L : List α)
    (hL : L.Nodup) (address : α → BirthAddress K) (ha : Function.Injective address)
    (values : α → ℕ) (a : α) (haL : a ∈ L) :
    pd5b_label (pcr_coordinateLog L address values) (address a) = some (values a) := by
  have hn : ((pcr_coordinateLog L address values).map Prod.fst).Nodup := by
    simpa [pcr_coordinateLog, List.map_map, Function.comp_def] using hL.map ha
  apply (pd5b_label_spec hn (address a) (values a)).2
  exact List.mem_map.mpr ⟨a, haL, rfl⟩

/-- Convert an instruction on an actual local log into a function of only earlier coordinates.
The filler at later coordinates is discarded by the strict-prefix filter before pick reads it. -/
noncomputable def pcr_coordinatePick {α : Type*} [LinearOrder α] {K : ℕ}
    (S : PDScale) (B : ℕ) (L : List α) (address : α → BirthAddress K)
    (pick : BirthAddress K → BirthLog K → ℕ) (pastLog : BirthLog K)
    (a : α) (earlier : {z : α // z < a} → ℕ) : ℕ :=
  pick (address a) ((pastLog ++ pcr_coordinateLog L address
    (fun z => if hz : z < a then earlier ⟨z, hz⟩ else 0)).filter
      (fun e => pd5_birthIndex S B e.1 < pd5_birthIndex S B (address a)))

/-- Performed flags and prescribed values are bounded by the triangular coordinate event. -/
theorem pcr_prescription_event_le {α : Type*} [Fintype α] [LinearOrder α] {K : ℕ}
    (S : PDScale) (B : ℕ) (L : List α) (hL : L.Nodup) (hcover : ∀ a, a ∈ L)
    (address : α → BirthAddress K) (hinj : Function.Injective address)
    (horder : ∀ a b, a < b ↔ pd5_birthIndex S B (address a) < pd5_birthIndex S B (address b))
    (U R : Finset (BirthAddress K)) (hRU : R ⊆ U)
    (pick : BirthAddress K → BirthLog K → ℕ) (pastLog : BirthLog K)
    (values : α → ℕ) (weights : α → ℝ) (hw : ∀ a, 0 ≤ weights a) :
    pd5_prescribedWeight S B U R pick pastLog (pcr_coordinateLog L address values) *
      (∏ a : α, weights a) ≤
        if ∀ a ∈ Finset.univ.filter (fun a => address a ∈ R),
          values a = pcr_coordinatePick S B L address pick pastLog a (fun z => values z.1)
        then ∏ a : α, weights a else 0 := by
  let log := pcr_coordinateLog L address values
  by_cases hcond : ∀ a ∈ U, ∃ p, pd5b_label log a = some p ∧
      (a ∈ R → p = pick a ((pastLog ++ log).filter fun e =>
        pd5_birthIndex S B e.1 < pd5_birthIndex S B a))
  · have hevent : ∀ a ∈ Finset.univ.filter (fun a => address a ∈ R),
        values a = pcr_coordinatePick S B L address pick pastLog a (fun z => values z.1) := by
      intro a ha
      have haR : address a ∈ R := (Finset.mem_filter.mp ha).2
      obtain ⟨p, hp, hforced⟩ := hcond (address a) (hRU haR)
      have hc : pd5b_label log (address a) = some (values a) :=
        pcr_coordinateLog_label L hL address hinj values a (hcover a)
      have heq : p = values a := Option.some.inj (hp.symm.trans hc)
      calc
        values a = p := heq.symm
        _ = pick (address a) ((pastLog ++ log).filter fun e =>
            pd5_birthIndex S B e.1 < pd5_birthIndex S B (address a)) := hforced haR
        _ = pcr_coordinatePick S B L address pick pastLog a (fun z => values z.1) := by
          unfold pcr_coordinatePick
          apply congrArg (pick (address a))
          rw [List.filter_append, List.filter_append]
          apply congrArg (fun l => (pastLog.filter fun e =>
            pd5_birthIndex S B e.1 < pd5_birthIndex S B (address a)) ++ l)
          apply pcr_coordinateLog_filter_congr S B L address values _ (address a)
          intro z hz hkey
          have hza : z < a := (horder z a).2 hkey
          simp [hza]
    have hweight : pd5_prescribedWeight S B U R pick pastLog
        (pcr_coordinateLog L address values) = 1 := by
      change (if ∀ a ∈ U, ∃ p, pd5b_label log a = some p ∧
        (a ∈ R → p = pick a ((pastLog ++ log).filter fun e =>
          pd5_birthIndex S B e.1 < pd5_birthIndex S B a)) then (1 : ℝ) else 0) = 1
      exact if_pos hcond
    rw [hweight, one_mul, if_pos hevent]
  · have hweight : pd5_prescribedWeight S B U R pick pastLog
        (pcr_coordinateLog L address values) = 0 := by
      change (if ∀ a ∈ U, ∃ p, pd5b_label log a = some p ∧
        (a ∈ R → p = pick a ((pastLog ++ log).filter fun e =>
          pd5_birthIndex S B e.1 < pd5_birthIndex S B a)) then (1 : ℝ) else 0) = 0
      exact if_neg hcond
    rw [hweight, zero_mul]
    split_ifs
    · exact Finset.prod_nonneg fun a _ => hw a
    · exact le_rfl

/-- Positive product choices with the literal local prescription cost one atom at each
forced coordinate that belongs to this operation. -/
theorem pcr_prescribed_product_sum_le {α : Type*} [Fintype α] [LinearOrder α] {K : ℕ}
    (S : PDScale) (B : ℕ) (L : List α) (hL : L.Nodup) (hcover : ∀ a, a ∈ L)
    (address : α → BirthAddress K) (hinj : Function.Injective address)
    (horder : ∀ a b, a < b ↔ pd5_birthIndex S B (address a) < pd5_birthIndex S B (address b))
    (P : α → Finset ℕ) (ν : α → ℕ → ℝ) (U R : Finset (BirthAddress K))
    (hRU : R ⊆ U) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (pick : BirthAddress K → BirthLog K → ℕ) (pastLog : BirthLog K)
    (hν : ∀ a p, p ∈ P a → 0 ≤ ν a p)
    (hatom : ∀ a, address a ∈ R → ∀ p ∈ P a, ν a p ≤ Δ) :
    (∑ b : (a : α) → {p : ℕ // p ∈ P a},
      pd5_prescribedWeight S B U R pick pastLog
        (pcr_coordinateLog L address (fun a => (b a : ℕ))) * ∏ a : α, ν a (b a)) ≤
      ∏ a : α, if address a ∈ R then Δ else ∑ p ∈ P a, ν a p := by
  let R₀ : Finset α := Finset.univ.filter fun a => address a ∈ R
  calc
    _ ≤ ∑ b : (a : α) → {p : ℕ // p ∈ P a},
        if ∀ a ∈ R₀, (b a : ℕ) =
          pcr_coordinatePick S B L address pick pastLog a (fun z => (b z.1 : ℕ))
        then ∏ a : α, ν a (b a) else 0 := by
      apply Finset.sum_le_sum
      intro b hb
      exact pcr_prescription_event_le S B L hL hcover address hinj horder U R hRU
        pick pastLog (fun a => (b a : ℕ)) (fun a => ν a (b a))
          (fun a => hν a (b a) (b a).property)
    _ ≤ ∏ a : α, if a ∈ R₀ then Δ else ∑ p ∈ P a, ν a p :=
      pcr_ordered_triangular_birth_sum_le P ν R₀ Δ hΔ
        (pcr_coordinatePick S B L address pick pastLog) hν
        (fun a ha p hp => hatom a (Finset.mem_filter.mp ha).2 p hp)
    _ = _ := by simp [R₀]

/-- A literal prescription pays one atom for every named forced address. If such an address
is absent from this operation its whole choice sum is zero. Free masses are bounded by M. -/
theorem pcr_prescribed_product_uniform_atom {α : Type*} [Fintype α] [LinearOrder α] {K : ℕ}
    (S : PDScale) (B : ℕ) (L : List α) (hL : L.Nodup) (hcover : ∀ a, a ∈ L)
    (address : α → BirthAddress K) (hinj : Function.Injective address)
    (horder : ∀ a b, a < b ↔ pd5_birthIndex S B (address a) < pd5_birthIndex S B (address b))
    (P : α → Finset ℕ) (ν : α → ℕ → ℝ) (U R : Finset (BirthAddress K))
    (hRU : R ⊆ U) (Δ M : ℝ) (hΔ : 0 ≤ Δ) (hM : 1 ≤ M)
    (pick : BirthAddress K → BirthLog K → ℕ) (pastLog : BirthLog K)
    (hν : ∀ a p, p ∈ P a → 0 ≤ ν a p)
    (hmass : ∀ a, (∑ p ∈ P a, ν a p) ≤ M)
    (hatom : ∀ a, address a ∈ R → ∀ p ∈ P a, ν a p ≤ Δ) :
    (∑ b : (a : α) → {p : ℕ // p ∈ P a},
      pd5_prescribedWeight S B U R pick pastLog
        (pcr_coordinateLog L address (fun a => (b a : ℕ))) * ∏ a : α, ν a (b a)) ≤
      Δ ^ R.card * M ^ Fintype.card α := by
  let A : Finset (BirthAddress K) := Finset.univ.image address
  let R₀ : Finset α := Finset.univ.filter fun a => address a ∈ R
  by_cases hR : R ⊆ A
  · have himage : R₀.image address = R := by
      ext r
      constructor
      · intro hr
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
        exact (Finset.mem_filter.mp ha).2
      · intro hr
        obtain ⟨a, ha, he⟩ := Finset.mem_image.mp (hR hr)
        apply Finset.mem_image.mpr
        refine ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, he⟩
        exact he.symm ▸ hr
    have hcard : R₀.card = R.card := by
      rw [← himage, Finset.card_image_of_injective _ hinj]
    calc
      _ ≤ ∏ a : α, if address a ∈ R then Δ else ∑ p ∈ P a, ν a p :=
        pcr_prescribed_product_sum_le S B L hL hcover address hinj horder P ν U R hRU
          Δ hΔ pick pastLog hν hatom
      _ ≤ ∏ a : α, if a ∈ R₀ then Δ else M := by
        apply Finset.prod_le_prod₀
        · intro a ha
          by_cases hr : address a ∈ R
          · simp [hr, hΔ]
          · simp only [if_neg hr]
            exact Finset.sum_nonneg fun p hp => hν a p hp
        · intro a ha
          by_cases hr : address a ∈ R
          · simp [R₀, hr]
          · simpa [R₀, hr] using hmass a
      _ = Δ ^ R₀.card * M ^ (Finset.univ \ R₀).card := by
        rw [Finset.prod_ite]
        have hyes : (Finset.univ.filter fun a : α => a ∈ R₀) = R₀ := by ext a; simp
        have hno : (Finset.univ.filter fun a : α => a ∉ R₀) = Finset.univ \ R₀ := by
          ext a; simp
        rw [hyes, hno]
        simp
      _ ≤ Δ ^ R.card * M ^ Fintype.card α := by
        rw [hcard]
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hΔ _)
        exact pow_le_pow_right₀ hM (Finset.card_le_univ _)
  · change ¬ (∀ r, r ∈ R → r ∈ A) at hR
    push_neg at hR
    obtain ⟨r, hr, hnot⟩ := hR
    have hwzero (b : (a : α) → {p : ℕ // p ∈ P a}) :
        pd5_prescribedWeight S B U R pick pastLog
          (pcr_coordinateLog L address (fun a => (b a : ℕ))) = 0 := by
      unfold pd5_prescribedWeight
      apply if_neg
      intro hcond
      obtain ⟨p, hp, _⟩ := hcond r (hRU hr)
      have hn : ((pcr_coordinateLog L address (fun a => (b a : ℕ))).map Prod.fst).Nodup := by
        simpa [pcr_coordinateLog, List.map_map, Function.comp_def] using hL.map hinj
      have hmem := (pd5b_label_spec hn r p).1 hp
      obtain ⟨a, ha, he⟩ := List.mem_map.mp hmem
      have headdr : address a = r := congrArg Prod.fst he
      apply hnot
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, headdr⟩
    simp_rw [hwzero, zero_mul]
    simp only [Finset.sum_const_zero]
    exact mul_nonneg (pow_nonneg hΔ _) (pow_nonneg (le_trans (by norm_num) hM) _)

end
end ArtinPrimitiveRoots.TypeII.PD
