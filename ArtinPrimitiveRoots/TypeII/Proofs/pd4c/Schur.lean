import ArtinPrimitiveRoots.TypeII.PD.Memory

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

noncomputable section

open Classical

theorem pd4c_finite_weighted_schur_norm {α : Type*} [DecidableEq α]
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

theorem pd4c_memOpNormLE_of_weighted_schur {K : ℕ} (F : PDFix K) (S : PDScale)
    (B : ℕ) (op : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ)
    (v₀ a b : ℝ) (hμ : ∀ s, 0 ≤ memMeasure F S s)
    (hμzero : ∀ s, ¬ MemValid F S s → memMeasure F S s = 0)
    (hv : ∀ s : MemPoint S.x K, 0 < v₀ ^ memSize s) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hrow : MemRowSchurLE F S B op v₀ a) (hcol : MemColSchurLE F S B op v₀ b)
    (hzero : ∀ s t, MemValid F S s → ¬ MemValid F S t → memKernel op s t = 0)
    (hrep : ∀ (T T' : Finset (MemPoint S.x K)) (f : MemPoint S.x K → ℂ),
      (∀ s, s ∉ T → f s = 0) → (∀ s ∈ T, memSize s ≤ B) →
      (∀ s ∈ T', memSize s ≤ B) → ∀ s ∈ T', MemValid F S s →
        op f s = ∑ t ∈ T,
          (if MemValid F S s ∧ MemValid F S t then memKernel op s t else 0) * f t) :
    MemOpNormLE F S B op (Real.sqrt (a * b)) := by
  classical
  intro T T' f hsupp hT hT'
  let k : MemPoint S.x K → MemPoint S.x K → ℂ := fun s t =>
    if MemValid F S s ∧ MemValid F S t then memKernel op s t else 0
  have hrow' : ∀ s ∈ T', ∑ t ∈ T, ‖k s t‖ * v₀ ^ memSize t ≤
      a * v₀ ^ memSize s := by
    intro s hsT'
    by_cases hsvalid : MemValid F S s
    · calc
        ∑ t ∈ T, ‖k s t‖ * v₀ ^ memSize t ≤
            ∑ t ∈ T, ‖memKernel op s t‖ * v₀ ^ memSize t := by
              apply Finset.sum_le_sum
              intro t ht
              by_cases htvalid : MemValid F S t
              · simp [k, hsvalid, htvalid]
              · simp [k, hsvalid, htvalid, hzero s t hsvalid htvalid]
        _ ≤ a * v₀ ^ memSize s := hrow s hsvalid (hT' s hsT') T hT
    · simp [k, hsvalid]
      exact mul_nonneg ha (hv s).le
  have hcol' : ∀ t ∈ T, ∑ s ∈ T', memMeasure F S s * ‖k s t‖ *
      v₀ ^ memSize s ≤ b * memMeasure F S t * v₀ ^ memSize t := by
    intro t htT
    by_cases htvalid : MemValid F S t
    · calc
        ∑ s ∈ T', memMeasure F S s * ‖k s t‖ * v₀ ^ memSize s =
            ∑ s ∈ T', memMeasure F S s * ‖memKernel op s t‖ *
              v₀ ^ memSize s := by
                apply Finset.sum_congr rfl
                intro s hsT'
                by_cases hsvalid : MemValid F S s
                · simp [k, hsvalid, htvalid]
                · simp [k, hsvalid, htvalid, hμzero s hsvalid]
        _ ≤ b * memMeasure F S t * v₀ ^ memSize t :=
            hcol t htvalid (hT t htT) T' hT'
    · have hμt := hμzero t htvalid
      simp [k, htvalid, hμt]
  have hschur := pd4c_finite_weighted_schur_norm (memMeasure F S)
    (fun s => v₀ ^ memSize s) k f T T' a b hμ hv ha hb hrow' hcol'
  have houtput : memNormSqOn F S T' (op f) =
      ∑ s ∈ T', memMeasure F S s *
        ‖∑ t ∈ T, k s t * f t‖ ^ 2 := by
    unfold memNormSqOn
    apply Finset.sum_congr rfl
    intro s hsT'
    by_cases hsvalid : MemValid F S s
    · rw [hrep T T' f hsupp hT hT' s hsT' hsvalid]
    · simp [hμzero s hsvalid]
  have hsqrt : (Real.sqrt (a * b)) ^ 2 = a * b :=
    Real.sq_sqrt (mul_nonneg ha hb)
  rw [houtput]
  unfold memNormSqOn
  calc
    (∑ s ∈ T', memMeasure F S s *
        ‖∑ t ∈ T, k s t * f t‖ ^ 2) ≤
      a * b * (∑ t ∈ T, memMeasure F S t * ‖f t‖ ^ 2) := hschur
    _ = (Real.sqrt (a * b)) ^ 2 *
        (∑ t ∈ T, memMeasure F S t * ‖f t‖ ^ 2) := by rw [hsqrt]
theorem pd4c_memOpNormLE_fintype_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
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


theorem pd4c_memNormSqOn_nonneg {K : ℕ} (F : PDFix K) (S : PDScale)
    (hμ : ∀ s, 0 ≤ memMeasure F S s) (T : Finset (MemPoint S.x K)) (f : MemPoint S.x K → ℂ) :
    0 ≤ memNormSqOn F S T f :=
  Finset.sum_nonneg fun s hs => mul_nonneg (hμ s) (sq_nonneg _)

theorem pd4c_memOpNormLE_mono {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (op : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (a b : ℝ)
    (hμ : ∀ s, 0 ≤ memMeasure F S s) (hop : MemOpNormLE F S B op a)
    (ha : 0 ≤ a) (hab : a ≤ b) : MemOpNormLE F S B op b := by
  intro T T' f hf hT hT'
  exact (hop T T' f hf hT hT').trans
    (mul_le_mul_of_nonneg_right (by nlinarith) (pd4c_memNormSqOn_nonneg F S hμ T f))

theorem pd4c_memRowSchurLE_mono {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (op : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (v a b : ℝ)
    (hv : 0 ≤ v) (hop : MemRowSchurLE F S B op v a) (hab : a ≤ b) :
    MemRowSchurLE F S B op v b := by
  intro s hs hsize T hT
  exact (hop s hs hsize T hT).trans (mul_le_mul_of_nonneg_right hab (pow_nonneg hv _))

theorem pd4c_memColSchurLE_mono {K : ℕ} (F : PDFix K) (S : PDScale) (B : ℕ)
    (op : (MemPoint S.x K → ℂ) → MemPoint S.x K → ℂ) (v a b : ℝ)
    (hv : 0 ≤ v) (hμ : ∀ s, 0 ≤ memMeasure F S s)
    (hop : MemColSchurLE F S B op v a) (hab : a ≤ b) : MemColSchurLE F S B op v b := by
  intro s hs hsize T hT
  exact (hop s hs hsize T hT).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hab (hμ s)) (pow_nonneg hv _))

end

end ArtinPrimitiveRoots.TypeII.PD
