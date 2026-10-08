import ArtinPrimitiveRoots.Theta.Proofs.TH_FAMILY_FIELDS.Defs

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)}
  {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}

private abbrev normSField (p : Sum S.Sf (InfinitePlace F)) : Type :=
  match p with
  | .inl v => v.1.adicCompletion F
  | .inr _ => ℂ

private instance normSField_instField (p : Sum S.Sf (InfinitePlace F)) :
    Field (normSField p) := by
  cases p <;> infer_instance

@[simp] private theorem upperM_zero_eq_one (K : Type) [Field K] : upperM K 0 = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [upperM]

@[simp] private theorem lowerM_zero_eq_one (K : Type) [Field K] : lowerM K 0 = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [lowerM]

@[simp] private theorem diagM_one_eq_one (K : Type) [Field K] : diagM K 1 = 1 := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [diagM]

private def normSAddAt : (p : Sum S.Sf (InfinitePlace F)) → normSField p → S.FS
  | .inl v, x => (fun v' => if h : v' = v then h.symm ▸ x else 0, fun _ => 0)
  | .inr w, x => (fun _ => 0, fun w' => if w' = w then x else 0)

private def normSUpperG (P : CoverPackage D S H A) (p : Sum S.Sf (InfinitePlace F))
    (x : normSField p) : P.tc.G :=
  P.tc.nS (Multiplicative.ofAdd (normSAddAt p x))

private noncomputable def normSUpperRP (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) : P.RP :=
  Classical.choose (P.nS_components (normSAddAt p x))

private theorem normSUpperRP_q (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) :
    P.q (normSUpperRP P p x) = normSUpperG P p x :=
  (Classical.choose_spec (P.nS_components (normSAddAt p x))).1

private theorem normSUpperRP_compF (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) (v : FinPlace F) :
    P.compF v (normSUpperRP P p x) =
      if hv : v ∈ S.Sf then (P.loc v).n
        (Multiplicative.ofAdd ((normSAddAt p x).1 ⟨v, hv⟩)) else 1 :=
  (Classical.choose_spec (P.nS_components (normSAddAt p x))).2.1 v

private theorem normSUpperRP_compC (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) (w : InfinitePlace F) :
    P.compC w (normSUpperRP P p x) =
      QuotientGroup.mk (upperM ℂ ((normSAddAt p x).2 w)) :=
  (Classical.choose_spec (P.nS_components (normSAddAt p x))).2.2 w

private abbrev normSUnitField (p : Sum S.Sf (InfinitePlace F)) := (normSField p)ˣ

private instance normSUnitField_instGroup (p : Sum S.Sf (InfinitePlace F)) :
    Group (normSUnitField p) := by
  cases p <;> infer_instance

private def normSNegOne : (p : Sum S.Sf (InfinitePlace F)) → normSUnitField p
  | .inl _ => -1
  | .inr _ => -1

private def normSNegFieldOne : (p : Sum S.Sf (InfinitePlace F)) → normSField p
  | .inl _ => -1
  | .inr _ => -1

private noncomputable def normSDiagData (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (u : normSUnitField p) : S.FSˣ :=
  match p with
  | .inl v => Classical.choose (P.emb_aS v u)
  | .inr w => S.atComplex w u

private theorem normSDiagData_compU_at (P : CoverPackage D S H A) (v : S.Sf)
    (u : normSUnitField (.inl v)) : S.compU v (normSDiagData P (.inl v) u) = u :=
  (Classical.choose_spec (P.emb_aS v u)).1

private theorem normSDiagData_compU_off (P : CoverPackage D S H A)
    (v₀ v : S.Sf) (u : normSUnitField (.inl v₀)) (h : v ≠ v₀) :
    S.compU v (normSDiagData P (.inl v₀) u) = 1 :=
  (Classical.choose_spec (P.emb_aS v₀ u)).2.1 v h

private theorem normSDiagData_compC_of_finite (P : CoverPackage D S H A)
    (v : S.Sf) (u : normSUnitField (.inl v)) (w : InfinitePlace F) :
    S.compC w (normSDiagData P (.inl v) u) = 1 :=
  (Classical.choose_spec (P.emb_aS v u)).2.2.1 w

private theorem normSDiagData_compU_of_complex (P : CoverPackage D S H A)
    (w : InfinitePlace F) (u : normSUnitField (.inr w)) (v : S.Sf) :
    S.compU v (normSDiagData P (.inr w) u) = 1 := by
  change S.compU v (S.atComplex w u) = 1
  ext <;> simp [SData.compU, SData.atComplex]

private theorem normSDiagData_compC_of_complex (P : CoverPackage D S H A)
    (w₀ w : InfinitePlace F) (u : normSUnitField (.inr w₀)) :
    S.compC w (normSDiagData P (.inr w₀) u) = if w = w₀ then u else 1 := by
  change S.compC w (S.atComplex w₀ u) = if w = w₀ then u else 1
  ext <;> by_cases h : w = w₀ <;> simp [SData.compC, SData.atComplex, h]

private def normSDiagG (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (u : normSUnitField p) : P.tc.G :=
  P.tc.aS (normSDiagData P p u)

private noncomputable def normSDiagRP (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (u : normSUnitField p) : P.RP :=
  Classical.choose (P.aS_components (normSDiagData P p u))

private theorem normSDiagRP_q (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (u : normSUnitField p) :
    P.q (normSDiagRP P p u) = normSDiagG P p u :=
  (Classical.choose_spec (P.aS_components (normSDiagData P p u))).1

private theorem normSDiagRP_compF (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (u : normSUnitField p) (v : FinPlace F) :
    P.compF v (normSDiagRP P p u) =
      if hv : v ∈ S.Sf then (P.loc v).a
        (S.compU ⟨v, hv⟩ (normSDiagData P p u)) else 1 :=
  (Classical.choose_spec (P.aS_components (normSDiagData P p u))).2.1 v

private theorem normSDiagRP_compC (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (u : normSUnitField p) (w : InfinitePlace F) :
    P.compC w (normSDiagRP P p u) =
      QuotientGroup.mk (diagM ℂ (S.compC w (normSDiagData P p u))) :=
  (Classical.choose_spec (P.aS_components (normSDiagData P p u))).2.2 w

private noncomputable def normSWeylRP (P : CoverPackage D S H A) : P.RP :=
  Classical.choose P.wS_components

private theorem normSWeylRP_q (P : CoverPackage D S H A) :
    P.q (normSWeylRP P) = P.tc.wS :=
  (Classical.choose_spec P.wS_components).1

private theorem normSWeylRP_compF (P : CoverPackage D S H A) (v : FinPlace F) :
    P.compF v (normSWeylRP P) = if hv : v ∈ S.Sf then (P.loc v).w else 1 :=
  (Classical.choose_spec P.wS_components).2.1 v

private theorem normSWeylRP_compC (P : CoverPackage D S H A) (w : InfinitePlace F) :
    P.compC w (normSWeylRP P) = QuotientGroup.mk (weylM ℂ) :=
  (Classical.choose_spec P.wS_components).2.2 w

private def normSLowerG (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) : P.tc.G :=
  P.tc.wS * normSUpperG P p x * P.tc.wS⁻¹

private noncomputable def normSLowerRP (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) : P.RP :=
  normSWeylRP P * normSUpperRP P p x * (normSWeylRP P)⁻¹

private theorem normSLowerRP_q (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) :
    P.q (normSLowerRP P p x) = normSLowerG P p x := by
  simp [normSLowerRP, normSLowerG, normSWeylRP_q, normSUpperRP_q]

private def normSWeylWordG (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) : P.tc.G :=
  normSUpperG P p 1 * normSLowerG P p (normSNegFieldOne p) * normSUpperG P p 1 *
    normSDiagG P p (normSNegOne p)

private def normSWeylWordRP (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) : P.RP :=
  normSUpperRP P p 1 * normSLowerRP P p (normSNegFieldOne p) * normSUpperRP P p 1 *
    normSDiagRP P p (normSNegOne p)

private theorem normSWeylWordRP_q (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) :
    P.q (normSWeylWordRP P p) = normSWeylWordG P p := by
  simp [normSWeylWordRP, normSWeylWordG, normSUpperRP_q, normSLowerRP_q, normSDiagRP_q]

private def normSLocalG (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) (u : normSUnitField p)
    (z : normSField p) (e : Bool) : P.tc.G :=
  normSLowerG P p x * normSDiagG P p u * normSUpperG P p z *
    (if e then normSWeylWordG P p else 1)

private noncomputable def normSLocalRP (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) (u : normSUnitField p)
    (z : normSField p) (e : Bool) : P.RP :=
  normSLowerRP P p x * normSDiagRP P p u * normSUpperRP P p z *
    (if e then normSWeylWordRP P p else 1)

private theorem normSLocalRP_q (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) (u : normSUnitField p)
    (z : normSField p) (e : Bool) :
    P.q (normSLocalRP P p x u z e) = normSLocalG P p x u z e := by
  cases e <;> simp [normSLocalRP, normSLocalG, normSLowerRP_q, normSDiagRP_q,
    normSUpperRP_q, normSWeylWordRP_q]

private theorem normSLocalG_mem (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) (u : normSUnitField p)
    (z : normSField p) (e : Bool) : normSLocalG P p x u z e ∈ P.tc.GS := by
  have hUpper (t : normSField p) : normSUpperG P p t ∈ P.tc.GS :=
    P.tc.nS_mem (Multiplicative.ofAdd (normSAddAt p t))
  have hDiag : normSDiagG P p u ∈ P.tc.GS := P.tc.aS_mem (normSDiagData P p u)
  have hLower (t : normSField p) : normSLowerG P p t ∈ P.tc.GS := by
    apply P.tc.GS.mul_mem
    · apply P.tc.GS.mul_mem
      · exact P.tc.wS_mem
      · exact hUpper t
    · exact P.tc.GS.inv_mem P.tc.wS_mem
  have hW : (if e then normSWeylWordG P p else 1) ∈ P.tc.GS := by
    cases e
    · simp
    · dsimp [normSWeylWordG]
      apply P.tc.GS.mul_mem
      · apply P.tc.GS.mul_mem
        · apply P.tc.GS.mul_mem
          · exact hUpper 1
          · exact hLower (normSNegFieldOne p)
        · exact hUpper 1
      · exact P.tc.aS_mem (normSDiagData P p (normSNegOne p))
  dsimp [normSLocalG]
  apply P.tc.GS.mul_mem
  · apply P.tc.GS.mul_mem
    · exact P.tc.GS.mul_mem (hLower x) hDiag
    · exact hUpper z
  · exact hW

private def normSProjectiveWord {K : Type} [Field K]
    (x : K) (u : Kˣ) (z : K) (e : Bool) : PGL2 K :=
  QuotientGroup.mk (lowerM K x) *
    QuotientGroup.mk (diagM K u) *
    QuotientGroup.mk (upperM K z) *
    (if e then QuotientGroup.mk (weylM K) else 1)

private def normSExpectedFinite (p : Sum S.Sf (InfinitePlace F))
    (x : normSField p) (u : normSUnitField p) (z : normSField p) (e : Bool)
    (v : S.Sf) : PGL2 (v.1.adicCompletion F) :=
  match p with
  | .inl v' =>
      if h : v' = v then h ▸ normSProjectiveWord x u z e else 1
  | .inr _ => 1

private def normSExpectedComplex (p : Sum S.Sf (InfinitePlace F))
    (x : normSField p) (u : normSUnitField p) (z : normSField p) (e : Bool)
    (w : InfinitePlace F) : PGL2 ℂ :=
  match p with
  | .inl _ => 1
  | .inr w' =>
      if w' = w then normSProjectiveWord x u z e else 1

private theorem list_map_prod_eq_one_of {α M : Type} [Monoid M]
    (l : List α) (f : α → M) (h : ∀ a ∈ l, f a = 1) :
    (l.map f).prod = 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [h a (by simp), one_mul]
      apply ih
      intro b hb
      exact h b (by simp [hb])

private theorem list_map_prod_eq_single_of {α M : Type} [DecidableEq α] [Monoid M]
    (l : List α) (f : α → M) (a : α) (hn : l.Nodup) (ha : a ∈ l)
    (h : ∀ b ∈ l, b ≠ a → f b = 1) :
    (l.map f).prod = f a := by
  induction l with
  | nil => cases ha
  | cons b l ih =>
      rcases List.nodup_cons.mp hn with ⟨hbnot, hnodup⟩
      by_cases hba : b = a
      · subst b
        have htail : (l.map f).prod = 1 := by
          apply list_map_prod_eq_one_of
          intro c hc
          apply h c (by simp [hc])
          intro hca
          subst c
          exact hbnot hc
        simp [htail]
      · have ha' : a ∈ l := by
          rcases List.mem_cons.mp ha with hab | ha'
          · exact False.elim (hba hab.symm)
          · exact ha'
        have hhead : f b = 1 := h b (by simp) hba
        have htail := ih hnodup ha' (by
          intro c hc hca
          exact h c (by simp [hc]) hca)
        simp [hhead, htail]

private theorem normSPGL2_weyl_conj {K : Type} [Field K] (x : K) :
    QuotientGroup.mk (weylM K) * QuotientGroup.mk (upperM K x) *
      (QuotientGroup.mk (weylM K) : PGL2 K)⁻¹ = QuotientGroup.mk (lowerM K x) := by
  have hW2 : weylM K * weylM K = 1 := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [weylM, Matrix.mul_apply]
  have hWq : (QuotientGroup.mk (weylM K) : PGL2 K) *
      QuotientGroup.mk (weylM K) = 1 := by
    change QuotientGroup.mk (weylM K * weylM K) = 1
    rw [hW2]
    simp
  have hWInv : (QuotientGroup.mk (weylM K) : PGL2 K)⁻¹ =
      QuotientGroup.mk (weylM K) := by
    calc
      (QuotientGroup.mk (weylM K) : PGL2 K)⁻¹ =
          (QuotientGroup.mk (weylM K))⁻¹ *
            (QuotientGroup.mk (weylM K) * QuotientGroup.mk (weylM K)) := by rw [hWq]; simp
      _ = ((QuotientGroup.mk (weylM K))⁻¹ * QuotientGroup.mk (weylM K)) *
            QuotientGroup.mk (weylM K) := by group
      _ = QuotientGroup.mk (weylM K) := by simp
  have hmat : weylM K * upperM K x * weylM K = lowerM K x := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [weylM, upperM, lowerM, Matrix.mul_apply]
  calc
    QuotientGroup.mk (weylM K) * QuotientGroup.mk (upperM K x) *
        (QuotientGroup.mk (weylM K) : PGL2 K)⁻¹ =
      QuotientGroup.mk (weylM K) * QuotientGroup.mk (upperM K x) *
        QuotientGroup.mk (weylM K) := by rw [hWInv]
    _ = QuotientGroup.mk (weylM K * upperM K x * weylM K) := by simp [mul_assoc]
    _ = QuotientGroup.mk (lowerM K x) := by rw [hmat]

private theorem normSUpperRP_pr_finite_at (P : CoverPackage D S H A) (v : S.Sf)
    (x : v.1.adicCompletion F) :
    (P.loc v.1).pr (P.compF v.1 (normSUpperRP P (.inl v) x)) =
      QuotientGroup.mk (upperM (v.1.adicCompletion F) x) := by
  rw [normSUpperRP_compF]
  simp only [dif_pos v.2]
  simpa [normSAddAt] using (P.loc v.1).pr_n x

private theorem normSUpperRP_pr_finite_off (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) (v : S.Sf)
    (h : p ≠ Sum.inl v) :
    (P.loc v.1).pr (P.compF v.1 (normSUpperRP P p x)) = 1 := by
  cases p with
  | inl v₀ =>
      have hne : v ≠ v₀ := by
        intro hv
        apply h
        simp [hv]
      rw [normSUpperRP_compF]
      simp only [dif_pos v.2]
      simpa [normSAddAt, hne, upperM_zero_eq_one] using (P.loc v.1).pr_n 0
  | inr w =>
      rw [normSUpperRP_compF]
      simp only [dif_pos v.2]
      simpa [normSAddAt, upperM_zero_eq_one] using (P.loc v.1).pr_n 0

private theorem normSUpperRP_compC_at (P : CoverPackage D S H A) (w : InfinitePlace F)
    (x : ℂ) :
    P.compC w (normSUpperRP P (.inr w) x) = QuotientGroup.mk (upperM ℂ x) := by
  rw [normSUpperRP_compC]
  simp [normSAddAt, upperM]

private theorem normSUpperRP_compC_off (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) (w : InfinitePlace F)
    (h : p ≠ Sum.inr w) :
    P.compC w (normSUpperRP P p x) = 1 := by
  cases p with
  | inl v =>
      rw [normSUpperRP_compC]
      simp [normSAddAt, upperM_zero_eq_one]
  | inr w₀ =>
      have hne : w ≠ w₀ := by
        intro hw
        apply h
        simp [hw]
      rw [normSUpperRP_compC]
      simp [normSAddAt, hne, upperM_zero_eq_one]

private theorem normSDiagRP_pr_finite_at (P : CoverPackage D S H A) (v : S.Sf)
    (u : (v.1.adicCompletion F)ˣ) :
  (P.loc v.1).pr (P.compF v.1 (normSDiagRP P (.inl v) u)) =
      QuotientGroup.mk (diagM (v.1.adicCompletion F) u) := by
  rw [normSDiagRP_compF]
  simp only [dif_pos v.2]
  have hcomp := normSDiagData_compU_at (P := P) v u
  rw [hcomp]
  rw [(P.loc v.1).pr_a]

private theorem normSDiagRP_pr_finite_off (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (u : normSUnitField p) (v : S.Sf)
    (h : p ≠ Sum.inl v) :
    (P.loc v.1).pr (P.compF v.1 (normSDiagRP P p u)) = 1 := by
  cases p with
  | inl v₀ =>
      have hne : v ≠ v₀ := by
        intro hv
        apply h
        simp [hv]
      rw [normSDiagRP_compF]
      simp only [dif_pos v.2]
      have hcomp := normSDiagData_compU_off (P := P) v₀ v u hne
      rw [hcomp]
      rw [(P.loc v.1).pr_a]
      simp [diagM_one_eq_one]
  | inr w =>
      rw [normSDiagRP_compF]
      simp only [dif_pos v.2]
      have hcomp := normSDiagData_compU_of_complex (P := P) w u v
      rw [hcomp]
      rw [(P.loc v.1).pr_a]
      simp [diagM_one_eq_one]

private theorem normSDiagRP_compC_at (P : CoverPackage D S H A) (w : InfinitePlace F)
    (u : ℂˣ) : P.compC w (normSDiagRP P (.inr w) u) = QuotientGroup.mk (diagM ℂ u) := by
  rw [normSDiagRP_compC]
  have hcomp := normSDiagData_compC_of_complex (P := P) w w u
  rw [hcomp]
  simp

private theorem normSDiagRP_compC_off (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (u : normSUnitField p) (w : InfinitePlace F)
    (h : p ≠ Sum.inr w) : P.compC w (normSDiagRP P p u) = 1 := by
  cases p with
  | inl v =>
      rw [normSDiagRP_compC]
      rw [normSDiagData_compC_of_finite P v u w]
      simp [diagM_one_eq_one]
  | inr w₀ =>
      have hne : w ≠ w₀ := by
        intro hw
        apply h
        simp [hw]
      rw [normSDiagRP_compC]
      rw [normSDiagData_compC_of_complex P w₀ w u]
      simp [hne, diagM_one_eq_one]

private theorem normSLowerRP_pr_finite_at (P : CoverPackage D S H A) (v : S.Sf)
    (x : v.1.adicCompletion F) :
    (P.loc v.1).pr (P.compF v.1 (normSLowerRP P (.inl v) x)) =
      QuotientGroup.mk (lowerM (v.1.adicCompletion F) x) := by
  simp only [normSLowerRP, map_mul, map_inv]
  rw [normSUpperRP_pr_finite_at]
  rw [normSWeylRP_compF]
  simp only [dif_pos v.2]
  rw [(P.loc v.1).pr_w]
  exact normSPGL2_weyl_conj x

private theorem normSLowerRP_pr_finite_off (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) (v : S.Sf)
    (h : p ≠ Sum.inl v) :
    (P.loc v.1).pr (P.compF v.1 (normSLowerRP P p x)) = 1 := by
  simp only [normSLowerRP, map_mul, map_inv]
  rw [normSUpperRP_pr_finite_off P p x v h]
  rw [normSWeylRP_compF]
  simp only [dif_pos v.2]
  rw [(P.loc v.1).pr_w]
  simp

private theorem normSLowerRP_compC_at (P : CoverPackage D S H A) (w : InfinitePlace F)
    (x : ℂ) :
    P.compC w (normSLowerRP P (.inr w) x) = QuotientGroup.mk (lowerM ℂ x) := by
  simp only [normSLowerRP, map_mul, map_inv]
  rw [normSUpperRP_compC_at]
  rw [normSWeylRP_compC]
  exact normSPGL2_weyl_conj x

private theorem normSLowerRP_compC_off (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) (w : InfinitePlace F)
    (h : p ≠ Sum.inr w) : P.compC w (normSLowerRP P p x) = 1 := by
  simp only [normSLowerRP, map_mul, map_inv]
  rw [normSUpperRP_compC_off P p x w h]
  rw [normSWeylRP_compC]
  simp

private theorem pgl2_pivot {K : Type} [Field K] (g : GL (Fin 2) K)
    (ha : (g : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0) :
    (QuotientGroup.mk g : PGL2 K) =
      (QuotientGroup.mk (lowerM K
        ((g : Matrix (Fin 2) (Fin 2) K) 1 0 / (g : Matrix (Fin 2) (Fin 2) K) 0 0)) *
      QuotientGroup.mk (diagM K
        ((Units.mk0 ((g : Matrix (Fin 2) (Fin 2) K) 0 0) ha) ^ 2 / g.det)) *
      QuotientGroup.mk (upperM K
        ((g : Matrix (Fin 2) (Fin 2) K) 0 1 / (g : Matrix (Fin 2) (Fin 2) K) 0 0)) : PGL2 K) := by
  let a := (g : Matrix (Fin 2) (Fin 2) K) 0 0
  let b := (g : Matrix (Fin 2) (Fin 2) K) 0 1
  let c := (g : Matrix (Fin 2) (Fin 2) K) 1 0
  let aU : Kˣ := Units.mk0 a ha
  let dU : Kˣ := g.det
  let x : K := c / a
  let y : Kˣ := aU ^ 2 / dU
  let z : K := b / a
  let s : Kˣ := dU / aU
  let w : GL (Fin 2) K := lowerM K x * diagM K y * upperM K z
  have hsval : (s : K) = (g.det : K) / a := by
    simp [s, dU, aU, a]
  have hdetVal : a * (g : Matrix (Fin 2) (Fin 2) K) 1 1 - b * c ≠ 0 := by
    simpa [a, b, c, Matrix.det_fin_two] using g.det_ne_zero
  have hdetVal' : a * (g : Matrix (Fin 2) (Fin 2) K) 1 1 - c * b ≠ 0 := by
    intro hz
    apply hdetVal
    rw [mul_comm b c]
    exact hz
  have hdetVal'' : (g : Matrix (Fin 2) (Fin 2) K) 1 1 * a - b * c ≠ 0 := by
    intro hz
    apply hdetVal
    rw [mul_comm a ((g : Matrix (Fin 2) (Fin 2) K) 1 1)]
    exact hz
  have hmat : g = Matrix.GeneralLinearGroup.scalar (Fin 2) s * w := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change (g : Matrix (Fin 2) (Fin 2) K) i j =
      (Matrix.scalar (Fin 2) (s : K) * (w : Matrix (Fin 2) (Fin 2) K)) i j
    rw [hsval]
    fin_cases i <;> fin_cases j <;>
      simp [a, b, c, aU, dU, x, y, z, s, w, lowerM, diagM, upperM,
        Matrix.scalar_apply, Matrix.mul_apply, Matrix.det_fin_two] <;>
      field_simp [ha, hdetVal, hdetVal', hdetVal'', a, b, c] <;> ring_nf
  have hratio : g / w = Matrix.GeneralLinearGroup.scalar (Fin 2) s := by
    calc
      g / w = (Matrix.GeneralLinearGroup.scalar (Fin 2) s * w) / w :=
        congrArg (fun t => t / w) hmat
      _ = Matrix.GeneralLinearGroup.scalar (Fin 2) s := by simp
  have hcenter : Matrix.GeneralLinearGroup.scalar (Fin 2) s ∈
      Subgroup.center (GL (Fin 2) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨s, rfl⟩
  change QuotientGroup.mk g = QuotientGroup.mk w
  apply (QuotientGroup.eq_iff_div_mem).2
  rw [hratio]
  exact hcenter

private theorem pgl2_weyl_word (K : Type) [Field K] :
    (QuotientGroup.mk (weylM K) : PGL2 K) =
      QuotientGroup.mk (upperM K 1) * QuotientGroup.mk (lowerM K (-1)) *
        QuotientGroup.mk (upperM K 1) * QuotientGroup.mk (diagM K (-1)) := by
  change QuotientGroup.mk (weylM K) =
    QuotientGroup.mk
      (upperM K 1 * lowerM K (-1) * upperM K 1 * diagM K (-1))
  have hmat : weylM K = upperM K 1 * lowerM K (-1) * upperM K 1 * diagM K (-1) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [weylM, upperM, lowerM, diagM, Matrix.mul_apply]
  rw [hmat]

private theorem normSLocalRP_compF_split (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) (u : normSUnitField p)
    (z : normSField p) (e : Bool) (v : FinPlace F) :
    P.compF v (normSLocalRP P p x u z e) =
      P.compF v (normSLowerRP P p x) * P.compF v (normSDiagRP P p u) *
        P.compF v (normSUpperRP P p z) *
          (if e then P.compF v (normSWeylWordRP P p) else 1) := by
  cases e <;> simp [normSLocalRP, map_mul]

private theorem normSLocalRP_compC_split (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) (u : normSUnitField p)
    (z : normSField p) (e : Bool) (w : InfinitePlace F) :
    P.compC w (normSLocalRP P p x u z e) =
      P.compC w (normSLowerRP P p x) * P.compC w (normSDiagRP P p u) *
        P.compC w (normSUpperRP P p z) *
          (if e then P.compC w (normSWeylWordRP P p) else 1) := by
  cases e <;> simp [normSLocalRP, map_mul]

private theorem normSWeylWordRP_pr_finite_at (P : CoverPackage D S H A)
    (v : S.Sf) :
    (P.loc v.1).pr (P.compF v.1 (normSWeylWordRP P (.inl v))) =
      QuotientGroup.mk (weylM (v.1.adicCompletion F)) := by
  simp only [normSWeylWordRP, map_mul, normSUpperRP_pr_finite_at,
    normSLowerRP_pr_finite_at, normSDiagRP_pr_finite_at,
    normSNegFieldOne, normSNegOne]
  exact (pgl2_weyl_word (v.1.adicCompletion F)).symm

private theorem normSWeylWordRP_pr_finite_off (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (v : S.Sf) (h : p ≠ Sum.inl v) :
    (P.loc v.1).pr (P.compF v.1 (normSWeylWordRP P p)) = 1 := by
  cases p with
  | inl v₀ =>
      simp only [normSWeylWordRP, map_mul,
        normSUpperRP_pr_finite_off P (.inl v₀) 1 v h,
        normSLowerRP_pr_finite_off P (.inl v₀) (normSNegFieldOne (.inl v₀)) v h,
        normSDiagRP_pr_finite_off P (.inl v₀) (normSNegOne (.inl v₀)) v h]
      simp
  | inr w =>
      simp only [normSWeylWordRP, map_mul,
        normSUpperRP_pr_finite_off P (.inr w) 1 v h,
        normSLowerRP_pr_finite_off P (.inr w) (normSNegFieldOne (.inr w)) v h,
        normSDiagRP_pr_finite_off P (.inr w) (normSNegOne (.inr w)) v h]
      simp

private theorem normSWeylWordRP_compC_at (P : CoverPackage D S H A)
    (w : InfinitePlace F) :
    P.compC w (normSWeylWordRP P (.inr w)) = QuotientGroup.mk (weylM ℂ) := by
  simp only [normSWeylWordRP, map_mul, normSUpperRP_compC_at,
    normSLowerRP_compC_at, normSDiagRP_compC_at,
    normSNegFieldOne, normSNegOne]
  exact (pgl2_weyl_word ℂ).symm

private theorem normSWeylWordRP_compC_off (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (w : InfinitePlace F) (h : p ≠ Sum.inr w) :
    P.compC w (normSWeylWordRP P p) = 1 := by
  cases p with
  | inl v =>
      simp only [normSWeylWordRP, map_mul,
        normSUpperRP_compC_off P (.inl v) 1 w h,
        normSLowerRP_compC_off P (.inl v) (normSNegFieldOne (.inl v)) w h,
        normSDiagRP_compC_off P (.inl v) (normSNegOne (.inl v)) w h]
      simp
  | inr w₀ =>
      simp only [normSWeylWordRP, map_mul,
        normSUpperRP_compC_off P (.inr w₀) 1 w h,
        normSLowerRP_compC_off P (.inr w₀) (normSNegFieldOne (.inr w₀)) w h,
        normSDiagRP_compC_off P (.inr w₀) (normSNegOne (.inr w₀)) w h]
      simp

private theorem normSLocalRP_pr_finite (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) (u : normSUnitField p)
    (z : normSField p) (e : Bool) (v : S.Sf) :
    (P.loc v.1).pr (P.compF v.1 (normSLocalRP P p x u z e)) =
      normSExpectedFinite p x u z e v := by
  rw [normSLocalRP_compF_split]
  cases p with
  | inl v₀ =>
      by_cases h : v₀ = v
      · subst v₀
        have hl := normSLowerRP_pr_finite_at P v x
        have hd := normSDiagRP_pr_finite_at P v u
        have hu := normSUpperRP_pr_finite_at P v z
        have hw := normSWeylWordRP_pr_finite_at P v
        cases e <;> simp [normSExpectedFinite, normSProjectiveWord, map_mul, hl, hd, hu, hw]
      · have hp : (Sum.inl v₀ : Sum S.Sf (InfinitePlace F)) ≠ Sum.inl v := by
          intro hh
          exact h (Sum.inl.inj hh)
        have hl := normSLowerRP_pr_finite_off P (.inl v₀) x v hp
        have hd := normSDiagRP_pr_finite_off P (.inl v₀) u v hp
        have hu := normSUpperRP_pr_finite_off P (.inl v₀) z v hp
        have hw := normSWeylWordRP_pr_finite_off P (.inl v₀) v hp
        cases e <;> simp [normSExpectedFinite, normSProjectiveWord, map_mul, h, hl, hd, hu, hw]
  | inr w =>
      have hp : (Sum.inr w : Sum S.Sf (InfinitePlace F)) ≠ Sum.inl v := by intro hh; cases hh
      have hl := normSLowerRP_pr_finite_off P (.inr w) x v hp
      have hd := normSDiagRP_pr_finite_off P (.inr w) u v hp
      have hu := normSUpperRP_pr_finite_off P (.inr w) z v hp
      have hw := normSWeylWordRP_pr_finite_off P (.inr w) v hp
      cases e <;> simp [normSExpectedFinite, normSProjectiveWord, map_mul, hl, hd, hu, hw]

private theorem normSLocalRP_pr_complex (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) (u : normSUnitField p)
    (z : normSField p) (e : Bool) (w : InfinitePlace F) :
    P.compC w (normSLocalRP P p x u z e) = normSExpectedComplex p x u z e w := by
  rw [normSLocalRP_compC_split]
  cases p with
  | inl v =>
      have hp : (Sum.inl v : Sum S.Sf (InfinitePlace F)) ≠ Sum.inr w := by intro hh; cases hh
      have hl := normSLowerRP_compC_off P (.inl v) x w hp
      have hd := normSDiagRP_compC_off P (.inl v) u w hp
      have hu := normSUpperRP_compC_off P (.inl v) z w hp
      have hw := normSWeylWordRP_compC_off P (.inl v) w hp
      cases e <;> simp [normSExpectedComplex, normSProjectiveWord, map_mul, hl, hd, hu, hw]
  | inr w₀ =>
      by_cases h : w₀ = w
      · subst w₀
        have hl := normSLowerRP_compC_at P w x
        have hd := normSDiagRP_compC_at P w u
        have hu := normSUpperRP_compC_at P w z
        have hw := normSWeylWordRP_compC_at P w
        cases e <;> simp [normSExpectedComplex, normSProjectiveWord, map_mul, hl, hd, hu, hw]
      · have hp : (Sum.inr w₀ : Sum S.Sf (InfinitePlace F)) ≠ Sum.inr w := by
          intro hh
          exact h (Sum.inr.inj hh)
        have hl := normSLowerRP_compC_off P (.inr w₀) x w hp
        have hd := normSDiagRP_compC_off P (.inr w₀) u w hp
        have hu := normSUpperRP_compC_off P (.inr w₀) z w hp
        have hw := normSWeylWordRP_compC_off P (.inr w₀) w hp
        cases e <;> simp [normSExpectedComplex, normSProjectiveWord, map_mul, h, hl, hd, hu, hw]

private theorem normSUpperRP_compF_exterior (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) (v : FinPlace F)
    (hv : v ∉ S.Sf) : P.compF v (normSUpperRP P p x) = 1 := by
  rw [normSUpperRP_compF]
  simp [hv]

private theorem normSDiagRP_compF_exterior (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (u : normSUnitField p) (v : FinPlace F)
    (hv : v ∉ S.Sf) : P.compF v (normSDiagRP P p u) = 1 := by
  rw [normSDiagRP_compF]
  simp [hv]

private theorem normSWeylRP_compF_exterior (P : CoverPackage D S H A) (v : FinPlace F)
    (hv : v ∉ S.Sf) : P.compF v (normSWeylRP P) = 1 := by
  rw [normSWeylRP_compF]
  simp [hv]

private theorem normSLowerRP_compF_exterior (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) (v : FinPlace F)
    (hv : v ∉ S.Sf) : P.compF v (normSLowerRP P p x) = 1 := by
  simp [normSLowerRP, map_mul, map_inv,
    normSWeylRP_compF_exterior P v hv, normSUpperRP_compF_exterior P p x v hv]

private theorem normSWeylWordRP_compF_exterior (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (v : FinPlace F) (hv : v ∉ S.Sf) :
    P.compF v (normSWeylWordRP P p) = 1 := by
  simp [normSWeylWordRP, map_mul,
    normSUpperRP_compF_exterior P p 1 v hv,
    normSLowerRP_compF_exterior P p (normSNegFieldOne p) v hv,
    normSDiagRP_compF_exterior P p (normSNegOne p) v hv]

private theorem normSLocalRP_compF_exterior (P : CoverPackage D S H A)
    (p : Sum S.Sf (InfinitePlace F)) (x : normSField p) (u : normSUnitField p)
    (z : normSField p) (e : Bool) (v : FinPlace F) (hv : v ∉ S.Sf) :
    P.compF v (normSLocalRP P p x u z e) = 1 := by
  cases e <;> simp [normSLocalRP, map_mul,
    normSLowerRP_compF_exterior P p x v hv,
    normSDiagRP_compF_exterior P p u v hv,
    normSUpperRP_compF_exterior P p z v hv,
    normSWeylWordRP_compF_exterior P p v hv]

private theorem normSUpperRP_compF_complex (P : CoverPackage D S H A)
    (w : InfinitePlace F) (x : ℂ) (v : S.Sf) :
    P.compF v.1 (normSUpperRP P (.inr w) x) = 1 := by
  rw [normSUpperRP_compF]
  simp only [dif_pos v.2]
  simp [normSAddAt]

private theorem normSUpperRP_compF_finite_off (P : CoverPackage D S H A)
    (v₀ v : S.Sf) (x : v₀.1.adicCompletion F) (h : v ≠ v₀) :
    P.compF v.1 (normSUpperRP P (.inl v₀) x) = 1 := by
  rw [normSUpperRP_compF]
  simp only [dif_pos v.2]
  simp [normSAddAt, h]

private theorem normSDiagRP_compF_finite_off (P : CoverPackage D S H A)
    (v₀ v : S.Sf) (u : (v₀.1.adicCompletion F)ˣ) (h : v ≠ v₀) :
    P.compF v.1 (normSDiagRP P (.inl v₀) u) = 1 := by
  rw [normSDiagRP_compF]
  simp only [dif_pos v.2]
  have hcomp := normSDiagData_compU_off (P := P) v₀ v u h
  rw [hcomp, (P.loc v.1).a_one]

private theorem normSLowerRP_compF_finite_off (P : CoverPackage D S H A)
    (v₀ v : S.Sf) (x : v₀.1.adicCompletion F) (h : v ≠ v₀) :
    P.compF v.1 (normSLowerRP P (.inl v₀) x) = 1 := by
  simp [normSLowerRP, map_mul, map_inv,
    normSWeylRP_compF, dif_pos v.2,
    normSUpperRP_compF_finite_off P v₀ v x h]

private theorem normSWeylWordRP_compF_finite_off (P : CoverPackage D S H A)
    (v₀ v : S.Sf) (h : v ≠ v₀) :
    P.compF v.1 (normSWeylWordRP P (.inl v₀)) = 1 := by
  simp [normSWeylWordRP, map_mul,
    normSUpperRP_compF_finite_off P v₀ v 1 h,
    normSLowerRP_compF_finite_off P v₀ v (normSNegFieldOne (.inl v₀)) h,
    normSDiagRP_compF_finite_off P v₀ v (normSNegOne (.inl v₀)) h]

private theorem normSLocalRP_compF_finite_off (P : CoverPackage D S H A)
    (v₀ v : S.Sf) (x : v₀.1.adicCompletion F) (u : (v₀.1.adicCompletion F)ˣ)
    (z : v₀.1.adicCompletion F) (e : Bool) (h : v ≠ v₀) :
    P.compF v.1 (normSLocalRP P (.inl v₀) x u z e) = 1 := by
  cases e <;> simp [normSLocalRP, map_mul,
    normSLowerRP_compF_finite_off P v₀ v x h,
    normSDiagRP_compF_finite_off P v₀ v u h,
    normSUpperRP_compF_finite_off P v₀ v z h,
    normSWeylWordRP_compF_finite_off P v₀ v h]

private theorem normSDiagRP_compF_complex (P : CoverPackage D S H A)
    (w : InfinitePlace F) (u : ℂˣ) (v : S.Sf) :
    P.compF v.1 (normSDiagRP P (.inr w) u) = 1 := by
  rw [normSDiagRP_compF]
  simp only [dif_pos v.2]
  rw [normSDiagData_compU_of_complex (P := P) w u v, (P.loc v.1).a_one]

private theorem normSLowerRP_compF_complex (P : CoverPackage D S H A)
    (w : InfinitePlace F) (x : ℂ) (v : S.Sf) :
    P.compF v.1 (normSLowerRP P (.inr w) x) = 1 := by
  simp [normSLowerRP, map_mul, map_inv, normSWeylRP_compF, dif_pos v.2,
    normSUpperRP_compF_complex P w x v]

private theorem normSWeylWordRP_compF_complex (P : CoverPackage D S H A)
    (w : InfinitePlace F) (v : S.Sf) :
    P.compF v.1 (normSWeylWordRP P (.inr w)) = 1 := by
  simp [normSWeylWordRP, normSNegOne, map_mul,
    normSUpperRP_compF_complex P w 1 v,
    normSLowerRP_compF_complex P w (normSNegFieldOne (.inr w)) v,
    normSDiagRP_compF_complex P w (-1) v]

private theorem normSLocalRP_compF_complex (P : CoverPackage D S H A)
    (w : InfinitePlace F) (x : ℂ) (u : ℂˣ) (z : ℂ) (e : Bool) (v : S.Sf) :
    P.compF v.1 (normSLocalRP P (.inr w) x u z e) = 1 := by
  cases e <;> simp [normSLocalRP, map_mul,
    normSLowerRP_compF_complex P w x v,
    normSDiagRP_compF_complex P w u v,
    normSUpperRP_compF_complex P w z v,
    normSWeylWordRP_compF_complex P w v]

/-- Every projective two by two matrix is a word in upper, lower, diagonal, and Weyl factors.
The Weyl factor is kept as a Boolean so a finite product of local factors can be assembled. -/
theorem thetaPGL2_elementary_word {K : Type} [Field K] (g : PGL2 K) :
    ∃ x : K, ∃ u : Kˣ, ∃ z : K, ∃ e : Bool,
      g = QuotientGroup.mk (lowerM K x) * QuotientGroup.mk (diagM K u) *
        QuotientGroup.mk (upperM K z) * (if e then QuotientGroup.mk (weylM K) else 1) := by
  obtain ⟨A, hA⟩ : ∃ A : GL (Fin 2) K, (QuotientGroup.mk A : PGL2 K) = g :=
    QuotientGroup.mk_surjective g
  let a := (A : Matrix (Fin 2) (Fin 2) K) 0 0
  let b := (A : Matrix (Fin 2) (Fin 2) K) 0 1
  by_cases ha : a ≠ 0
  · let x := (A : Matrix (Fin 2) (Fin 2) K) 1 0 /
        (A : Matrix (Fin 2) (Fin 2) K) 0 0
    let u := (Units.mk0 ((A : Matrix (Fin 2) (Fin 2) K) 0 0) ha) ^ 2 / A.det
    let z := (A : Matrix (Fin 2) (Fin 2) K) 0 1 /
        (A : Matrix (Fin 2) (Fin 2) K) 0 0
    have h := pgl2_pivot A ha
    refine ⟨x, u, z, false, ?_⟩
    rw [← hA]
    simpa using h
  · have hb : b ≠ 0 := by
      have hd := A.det_ne_zero
      rw [Matrix.det_fin_two] at hd
      have hA00 : (A : Matrix (Fin 2) (Fin 2) K) 0 0 = 0 := by
        exact not_ne_iff.mp ha
      rw [hA00] at hd
      simp only [zero_mul, zero_sub] at hd
      have hbc :
          ((A : Matrix (Fin 2) (Fin 2) K) 0 1) *
            ((A : Matrix (Fin 2) (Fin 2) K) 1 0) ≠ 0 := neg_ne_zero.mp hd
      exact (mul_ne_zero_iff.mp hbc).1
    let W := weylM K
    have hW2 : W * W = 1 := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [W, weylM, Matrix.mul_apply]
    let g' := A * W
    have htop : (g' : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
      dsimp [g', W, weylM]
      simpa [Matrix.mul_apply] using hb
    let x := (g' : Matrix (Fin 2) (Fin 2) K) 1 0 /
        (g' : Matrix (Fin 2) (Fin 2) K) 0 0
    let u := (Units.mk0 ((g' : Matrix (Fin 2) (Fin 2) K) 0 0) htop) ^ 2 / g'.det
    let z := (g' : Matrix (Fin 2) (Fin 2) K) 0 1 /
        (g' : Matrix (Fin 2) (Fin 2) K) 0 0
    have h := pgl2_pivot g' htop
    refine ⟨x, u, z, true, ?_⟩
    have hg' : QuotientGroup.mk g' =
        QuotientGroup.mk (lowerM K x) * QuotientGroup.mk (diagM K u) *
          QuotientGroup.mk (upperM K z) := h
    have hmul : (QuotientGroup.mk A : PGL2 K) =
        QuotientGroup.mk (A * W) * QuotientGroup.mk W := by
      calc
        QuotientGroup.mk A = QuotientGroup.mk (A * (W * W)) := by simp [hW2]
        _ = QuotientGroup.mk ((A * W) * W) := by rw [mul_assoc]
        _ = QuotientGroup.mk (A * W) * QuotientGroup.mk W := by
          rw [QuotientGroup.mk_mul]
    calc
      g = QuotientGroup.mk A := hA.symm
      _ = QuotientGroup.mk g' * QuotientGroup.mk W := by
        simpa [g', W] using hmul
      _ = QuotientGroup.mk (lowerM K x) * QuotientGroup.mk (diagM K u) *
          QuotientGroup.mk (upperM K z) * QuotientGroup.mk (weylM K) := by
        rw [hg']

private structure NormSWordData (K : Type) [Field K] (g : PGL2 K) where
  x : K
  u : Kˣ
  z : K
  e : Bool
  spec : g = QuotientGroup.mk (lowerM K x) * QuotientGroup.mk (diagM K u) *
    QuotientGroup.mk (upperM K z) * (if e then QuotientGroup.mk (weylM K) else 1)

private noncomputable def normSWordData {K : Type} [Field K] (g : PGL2 K) :
    NormSWordData K g := by
  classical
  have hdata : Nonempty (NormSWordData K g) := by
    rcases thetaPGL2_elementary_word g with ⟨x, u, z, e, h⟩
    exact ⟨⟨x, u, z, e, h⟩⟩
  exact Classical.choice hdata

private noncomputable def normSFiniteFactor (P : CoverPackage D S H A)
    (r : P.RP) (v : S.Sf) : P.RP := by
  let d := normSWordData ((P.loc v.1).pr (P.compF v.1 r))
  exact normSLocalRP P (.inl v) d.x d.u d.z d.e

private noncomputable def normSComplexFactor (P : CoverPackage D S H A)
    (r : P.RP) (w : InfinitePlace F) : P.RP := by
  let d := normSWordData (P.compC w r)
  exact normSLocalRP P (.inr w) d.x d.u d.z d.e

private noncomputable def normSSupportedRP (P : CoverPackage D S H A) (r : P.RP) : P.RP :=
  (S.Sf.attach.toList.map (normSFiniteFactor P r)).prod *
    ((Finset.univ : Finset (InfinitePlace F)).toList.map (normSComplexFactor P r)).prod

private theorem list_prod_mem_subgroup {G : Type} [Group G] (H : Subgroup G)
    {α : Type} (l : List α) (f : α → G) (hf : ∀ a ∈ l, f a ∈ H) :
    (l.map f).prod ∈ H := by
  induction l with
  | nil => simpa using H.one_mem
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      exact H.mul_mem (hf a (by simp)) (ih (by
        intro b hb
        exact hf b (by simp [hb])))

private theorem normSSupportedRP_q_mem (P : CoverPackage D S H A) (r : P.RP) :
    P.q (normSSupportedRP P r) ∈ P.tc.GS := by
  let fF : S.Sf → P.tc.G := fun v =>
    normSLocalG P (.inl v)
      (normSWordData ((P.loc v.1).pr (P.compF v.1 r))).x
      (normSWordData ((P.loc v.1).pr (P.compF v.1 r))).u
      (normSWordData ((P.loc v.1).pr (P.compF v.1 r))).z
      (normSWordData ((P.loc v.1).pr (P.compF v.1 r))).e
  have hfiniteMem : (S.Sf.attach.toList.map fF).prod ∈ P.tc.GS := by
    apply list_prod_mem_subgroup (G := P.tc.G) P.tc.GS S.Sf.attach.toList fF
    intro v hv
    exact normSLocalG_mem P (.inl v)
      (normSWordData ((P.loc v.1).pr (P.compF v.1 r))).x
      (normSWordData ((P.loc v.1).pr (P.compF v.1 r))).u
      (normSWordData ((P.loc v.1).pr (P.compF v.1 r))).z
      (normSWordData ((P.loc v.1).pr (P.compF v.1 r))).e
  have hfinite : P.q ((S.Sf.attach.toList.map (normSFiniteFactor P r)).prod) ∈ P.tc.GS := by
    rw [map_list_prod, List.map_map]
    simpa [fF, normSFiniteFactor, Function.comp_def, normSLocalRP_q] using hfiniteMem
  let fC : InfinitePlace F → P.tc.G := fun w =>
    normSLocalG P (.inr w) (normSWordData (P.compC w r)).x
      (normSWordData (P.compC w r)).u (normSWordData (P.compC w r)).z
      (normSWordData (P.compC w r)).e
  have hcomplexMem : ((Finset.univ : Finset (InfinitePlace F)).toList.map fC).prod ∈
      P.tc.GS := by
    apply list_prod_mem_subgroup (G := P.tc.G) P.tc.GS
      (Finset.univ : Finset (InfinitePlace F)).toList fC
    intro w hw
    exact normSLocalG_mem P (.inr w) (normSWordData (P.compC w r)).x
      (normSWordData (P.compC w r)).u (normSWordData (P.compC w r)).z
      (normSWordData (P.compC w r)).e
  have hcomplex : P.q (((Finset.univ : Finset (InfinitePlace F)).toList.map
      (normSComplexFactor P r)).prod) ∈ P.tc.GS := by
    rw [map_list_prod, List.map_map]
    simpa [fC, normSComplexFactor, Function.comp_def, normSLocalRP_q] using hcomplexMem
  change P.q ((S.Sf.attach.toList.map (normSFiniteFactor P r)).prod *
    ((Finset.univ : Finset (InfinitePlace F)).toList.map (normSComplexFactor P r)).prod) ∈ _
  rw [map_mul]
  exact P.tc.GS.mul_mem hfinite hcomplex

private theorem normSSupportedRP_compF_exterior (P : CoverPackage D S H A)
    (r : P.RP) (v : FinPlace F) (hv : v ∉ S.Sf) :
    P.compF v (normSSupportedRP P r) = 1 := by
  rw [normSSupportedRP, map_mul, map_list_prod, map_list_prod]
  have hfinite : (S.Sf.attach.toList.map fun v₀ => P.compF v (normSFiniteFactor P r v₀)).prod = 1 := by
    apply list_map_prod_eq_one_of
    intro v₀ hv₀
    exact normSLocalRP_compF_exterior P (.inl v₀)
      (normSWordData ((P.loc v₀.1).pr (P.compF v₀.1 r))).x
      (normSWordData ((P.loc v₀.1).pr (P.compF v₀.1 r))).u
      (normSWordData ((P.loc v₀.1).pr (P.compF v₀.1 r))).z
      (normSWordData ((P.loc v₀.1).pr (P.compF v₀.1 r))).e v hv
  have hcomplex : ((Finset.univ : Finset (InfinitePlace F)).toList.map
      fun w => P.compF v (normSComplexFactor P r w)).prod = 1 := by
    apply list_map_prod_eq_one_of
    intro w hw
    exact normSLocalRP_compF_exterior P (.inr w)
      (normSWordData (P.compC w r)).x (normSWordData (P.compC w r)).u
      (normSWordData (P.compC w r)).z (normSWordData (P.compC w r)).e v hv
  simpa only [List.map_map, Function.comp_def] using
    (show (S.Sf.attach.toList.map fun v₀ => P.compF v (normSFiniteFactor P r v₀)).prod *
      ((Finset.univ : Finset (InfinitePlace F)).toList.map
        fun w => P.compF v (normSComplexFactor P r w)).prod = 1 by rw [hfinite, hcomplex]; simp)

private theorem normSSupportedRP_compC (P : CoverPackage D S H A)
    (r : P.RP) (w : InfinitePlace F) :
    P.compC w (normSSupportedRP P r) = P.compC w r := by
  classical
  rw [normSSupportedRP, map_mul, map_list_prod, map_list_prod]
  have hfinite : (S.Sf.attach.toList.map fun v => P.compC w (normSFiniteFactor P r v)).prod = 1 := by
    apply list_map_prod_eq_one_of
    intro v hv
    let d := normSWordData ((P.loc v.1).pr (P.compF v.1 r))
    change P.compC w (normSLocalRP P (.inl v) d.x d.u d.z d.e) = 1
    simpa [normSExpectedComplex] using
      (normSLocalRP_pr_complex P (.inl v) d.x d.u d.z d.e w)
  have hcomplex : ((Finset.univ : Finset (InfinitePlace F)).toList.map
      fun w₀ => P.compC w (normSComplexFactor P r w₀)).prod = P.compC w r := by
    let f : InfinitePlace F → PGL2 ℂ := fun w₀ =>
      P.compC w (normSComplexFactor P r w₀)
    have hsingle : ((Finset.univ : Finset (InfinitePlace F)).toList.map f).prod = f w := by
      apply list_map_prod_eq_single_of
      · exact Finset.nodup_toList (Finset.univ : Finset (InfinitePlace F))
      · simp
      · intro w₀ hw₀ hne
        let d := normSWordData (P.compC w₀ r)
        have hne' : w₀ ≠ w := hne
        change P.compC w (normSLocalRP P (.inr w₀) d.x d.u d.z d.e) = 1
        simpa [normSExpectedComplex, hne'] using
          (normSLocalRP_pr_complex P (.inr w₀) d.x d.u d.z d.e w)
    rw [hsingle]
    let d := normSWordData (P.compC w r)
    change P.compC w (normSLocalRP P (.inr w) d.x d.u d.z d.e) = P.compC w r
    have hlocal := normSLocalRP_pr_complex P (.inr w) d.x d.u d.z d.e w
    simpa [normSExpectedComplex, normSProjectiveWord, d.spec] using hlocal
  simpa only [List.map_map, Function.comp_def] using
    (show (S.Sf.attach.toList.map fun v => P.compC w (normSFiniteFactor P r v)).prod *
      ((Finset.univ : Finset (InfinitePlace F)).toList.map
        fun w₀ => P.compC w (normSComplexFactor P r w₀)).prod = P.compC w r by
      rw [hfinite, one_mul, hcomplex])

private theorem normSSupportedRP_pr_finite (P : CoverPackage D S H A)
    (r : P.RP) (v : S.Sf) :
    (P.loc v.1).pr (P.compF v.1 (normSSupportedRP P r)) =
      (P.loc v.1).pr (P.compF v.1 r) := by
  classical
  let π : P.RP →* PGL2 (v.1.adicCompletion F) :=
    (P.loc v.1).pr.comp (P.compF v.1)
  change π (normSSupportedRP P r) = π r
  rw [normSSupportedRP]
  let f : S.Sf → PGL2 (v.1.adicCompletion F) := fun v₀ =>
    (P.loc v.1).pr (P.compF v.1 (normSFiniteFactor P r v₀))
  have hfinite : (S.Sf.attach.toList.map f).prod = (P.loc v.1).pr (P.compF v.1 r) := by
    have hsingle : (S.Sf.attach.toList.map f).prod = f v := by
      apply list_map_prod_eq_single_of
      · exact Finset.nodup_toList S.Sf.attach
      · simp
      · intro v₀ hv₀ hne
        let d := normSWordData ((P.loc v₀.1).pr (P.compF v₀.1 r))
        have hp : (Sum.inl v₀ : Sum S.Sf (InfinitePlace F)) ≠ Sum.inl v := by
          intro hh
          exact hne (Sum.inl.inj hh)
        change (P.loc v.1).pr
          (P.compF v.1 (normSLocalRP P (.inl v₀) d.x d.u d.z d.e)) = 1
        have hlocal := normSLocalRP_pr_finite P (.inl v₀) d.x d.u d.z d.e v
        simpa [normSExpectedFinite, hne] using hlocal
    have hAt : f v = (P.loc v.1).pr (P.compF v.1 r) := by
      let d := normSWordData ((P.loc v.1).pr (P.compF v.1 r))
      change (P.loc v.1).pr
        (P.compF v.1 (normSLocalRP P (.inl v) d.x d.u d.z d.e)) = _
      have hlocal := normSLocalRP_pr_finite P (.inl v) d.x d.u d.z d.e v
      simpa [normSExpectedFinite, normSProjectiveWord, d.spec] using hlocal
    exact hsingle.trans hAt
  have hcomplex : ((Finset.univ : Finset (InfinitePlace F)).toList.map
      fun w => (P.loc v.1).pr (P.compF v.1 (normSComplexFactor P r w))).prod = 1 := by
    apply list_map_prod_eq_one_of
    intro w hw
    let d := normSWordData (P.compC w r)
    change (P.loc v.1).pr (P.compF v.1 (normSLocalRP P (.inr w) d.x d.u d.z d.e)) = 1
    simpa [normSExpectedFinite] using
      (normSLocalRP_pr_finite P (.inr w) d.x d.u d.z d.e v)
  simp only [map_mul, map_list_prod, List.map_map, Function.comp_def]
  have hfiniteπ : (S.Sf.attach.toList.map
      (fun x => π (normSFiniteFactor P r x))).prod = π r := by
    simpa [f, π] using hfinite
  have hcomplexπ : ((Finset.univ : Finset (InfinitePlace F)).toList.map
      (fun x => π (normSComplexFactor P r x))).prod = 1 := by
    simpa [π] using hcomplex
  rw [hfiniteπ, hcomplexπ]
  simp

noncomputable def normSExteriorProductRP (P : CoverPackage D S H A)
    (r : P.RP) (T : Finset (FinPlace F)) : P.RP :=
  (T.toList.map fun v => P.incl v (P.compF v r)).prod

theorem normSExteriorProductRP_compF (P : CoverPackage D S H A)
    (r : P.RP) (T : Finset (FinPlace F)) (v : FinPlace F) :
    P.compF v (normSExteriorProductRP P r T) =
      if v ∈ T then P.compF v r else 1 := by
  classical
  rw [normSExteriorProductRP, map_list_prod]
  simp only [List.map_map, Function.comp_def]
  by_cases hv : v ∈ T
  · have hsingle : (T.toList.map fun v₀ => P.compF v (P.incl v₀ (P.compF v₀ r))).prod =
        P.compF v (P.incl v (P.compF v r)) := by
      apply list_map_prod_eq_single_of
      · exact Finset.nodup_toList T
      · simpa using hv
      · intro v₀ hv₀ hne
        have hne' : v₀ ≠ v := by
          intro hh
          exact hne hh
        rw [P.incl_compF_other v₀ v hne' (P.compF v₀ r)]
    rw [hsingle, P.incl_compF]
    simp [hv]
  · have hone : (T.toList.map fun v₀ => P.compF v (P.incl v₀ (P.compF v₀ r))).prod = 1 := by
      apply list_map_prod_eq_one_of
      intro v₀ hv₀
      have hne' : v₀ ≠ v := by
        intro hh
        subst v₀
        exact hv (Finset.mem_toList.mp hv₀)
      rw [P.incl_compF_other v₀ v hne' (P.compF v₀ r)]
    rw [hone]
    simp [hv]

theorem normSExteriorProductRP_compC (P : CoverPackage D S H A)
    (r : P.RP) (T : Finset (FinPlace F)) (w : InfinitePlace F) :
    P.compC w (normSExteriorProductRP P r T) = 1 := by
  rw [normSExteriorProductRP, map_list_prod]
  simp only [List.map_map, Function.comp_def]
  apply list_map_prod_eq_one_of
  intro v hv
  rw [P.incl_compC]

theorem normSExteriorProductRP_q (P : CoverPackage D S H A)
    (r : P.RP) (T : Finset (FinPlace F)) :
    P.q (normSExteriorProductRP P r T) =
      (T.toList.map fun v => P.emb v (P.compF v r)).prod := by
  rw [normSExteriorProductRP, map_list_prod, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro v hv
  simp only [Function.comp_apply]
  rw [P.q_incl]

theorem thetaNormalization_tameTail (P : CoverPackage D S H A) (r : P.RP) :
    ∃ T : Finset (FinPlace F), ∃ tail : P.RP,
      (∀ v ∈ T, v ∉ S.Sf) ∧
      (∀ v (hv : v ∉ S.Sf), P.compF v tail ∈ (P.tame v hv).Kmax) ∧
      (∀ v : S.Sf, P.compF v.1 tail = 1) ∧
      (∀ v ∈ T, P.compF v tail = 1) ∧
      (∀ w, P.compC w tail = 1) ∧
      (∀ v (hv : v ∉ S.Sf), v ∉ T → P.compF v tail = P.compF v r) := by
  classical
  let bad := P.comp_restricted r
  let T := bad.toFinset
  have hTmem (v : FinPlace F) : v ∈ T ↔
      ∃ hv : v ∉ S.Sf, P.compF v r ∉ (P.tame v hv).Kmax := by
    simp [T, bad]
  let lf : ∀ v : FinPlace F, (P.loc v).L := fun v =>
    if hv : v ∈ S.Sf then 1 else if v ∈ T then 1 else P.compF v r
  have hlf (v : FinPlace F) (hv : v ∉ S.Sf) :
      lf v ∈ (P.tame v hv).Kmax := by
    by_cases hT : v ∈ T
    · simp [lf, hv, hT]
    · have hr : P.compF v r ∈ (P.tame v hv).Kmax := by
        by_contra hnot
        apply hT
        exact (hTmem v).2 ⟨hv, hnot⟩
      simpa [lf, hv, hT] using hr
  have hrestricted : Set.Finite {v : FinPlace F | ∃ hv : v ∉ S.Sf,
      lf v ∉ (P.tame v hv).Kmax} := by
    apply Set.finite_empty.subset
    intro v hvbad
    rcases hvbad with ⟨hv, hnot⟩
    exact (hnot (hlf v hv)).elim
  obtain ⟨tail, htailF, htailC⟩ := P.comp_surj lf (fun _ => 1) hrestricted
  refine ⟨T, tail, ?_, ?_, ?_, ?_, htailC, ?_⟩
  · intro v hv
    exact (hTmem v).1 hv |>.1
  · intro v hv
    rw [htailF v]
    exact hlf v hv
  · intro v
    rw [htailF v.1]
    simp [lf, v.2]
  · intro v hv
    rw [htailF v]
    have hvS : v ∉ S.Sf := (hTmem v).1 hv |>.1
    simp [lf, hvS, hv]
  · intro v hv hnotT
    rw [htailF v]
    simp [lf, hv, hnotT]

theorem thetaNormalization_supportedRP {P : CoverPackage D S H A} (r : P.RP) :
    ∃ s : P.RP, P.q s ∈ P.tc.GS ∧
      (∀ v : S.Sf, (P.loc v.1).pr (P.compF v.1 s) = (P.loc v.1).pr (P.compF v.1 r)) ∧
      (∀ w, P.compC w s = P.compC w r) ∧
      (∀ v, v ∉ S.Sf → P.compF v s = 1) := by
  refine ⟨normSSupportedRP P r, normSSupportedRP_q_mem P r,
    normSSupportedRP_pr_finite P r, normSSupportedRP_compC P r, ?_⟩
  exact normSSupportedRP_compF_exterior P r

theorem thetaNormalization_supportedCentralPhase {P : CoverPackage D S H A}
    (r s : P.RP)
    (hproj : ∀ v : S.Sf, (P.loc v.1).pr (P.compF v.1 s) =
      (P.loc v.1).pr (P.compF v.1 r)) :
    ∀ v : S.Sf, ∃ ζ : rootsOfUnity 3 ℂ,
      P.compF v.1 r = (P.loc v.1).z ζ * P.compF v.1 s := by
  intro v
  have hpr := hproj v
  have hker : (P.loc v.1).pr
      (P.compF v.1 r * (P.compF v.1 s)⁻¹) = 1 := by
    rw [(P.loc v.1).pr.map_mul, (P.loc v.1).pr.map_inv, ← hpr]
    simp
  have hrange : P.compF v.1 r * (P.compF v.1 s)⁻¹ ∈ (P.loc v.1).pr.ker := hker
  rw [(P.loc v.1).pr_ker] at hrange
  rcases hrange with ⟨ζ, hζ⟩
  refine ⟨ζ, ?_⟩
  calc
    P.compF v.1 r =
        (P.compF v.1 r * (P.compF v.1 s)⁻¹) * P.compF v.1 s := by group
    _ = (P.loc v.1).z ζ * P.compF v.1 s := by rw [← hζ]

theorem thetaNormalization_centerLift_q {P : CoverPackage D S H A}
    (phase : S.Sf → rootsOfUnity 3 ℂ) (zRP : P.RP)
    (hF : ∀ v : FinPlace F, P.compF v zRP =
      if hv : v ∈ S.Sf then (P.loc v).z (phase ⟨v, hv⟩) else 1)
    (hC : ∀ w, P.compC w zRP = 1) :
    ∃ ξ : rootsOfUnity 3 ℂ, P.q zRP = P.tc.z ξ := by
  classical
  by_cases hS : S.Sf.Nonempty
  · obtain ⟨v₀, hv₀S⟩ := hS
    let b : FinPlace F → rootsOfUnity 3 ℂ := fun v =>
      if hv : v ∈ S.Sf then phase ⟨v, hv⟩ else 1
    let ξ : rootsOfUnity 3 ℂ := ∏ v ∈ S.Sf, b v
    let α : FinPlace F → rootsOfUnity 3 ℂ := fun v =>
      if hv : v ∈ S.Sf then
        if v = v₀ then b v / ξ else b v
      else 1
    have hErase : (∏ v ∈ S.Sf.erase v₀, b v) * b v₀ = ξ := by
      simpa [ξ] using (Finset.prod_erase_mul S.Sf b hv₀S)
    have hAlphaErase : ∏ v ∈ S.Sf.erase v₀, α v =
        ∏ v ∈ S.Sf.erase v₀, b v := by
      apply Finset.prod_congr rfl
      intro v hv
      rcases Finset.mem_erase.mp hv with ⟨hne, hvS⟩
      simp [α, b, hne, hvS]
    have hAlphaFin : ∏ v ∈ S.Sf, α v = 1 := by
      calc
        ∏ v ∈ S.Sf, α v =
            (∏ v ∈ S.Sf.erase v₀, α v) * α v₀ := by
              symm
              exact Finset.prod_erase_mul S.Sf α hv₀S
        _ = (∏ v ∈ S.Sf.erase v₀, b v) * (b v₀ / ξ) := by
              rw [hAlphaErase]
              simp [α, b, hv₀S]
        _ = 1 := by
              have hrewrite :
                  (∏ v ∈ S.Sf.erase v₀, b v) * (b v₀ / ξ) =
                    ((∏ v ∈ S.Sf.erase v₀, b v) * b v₀) / ξ := by
                simp [div_eq_mul_inv, mul_left_comm, mul_comm]
              rw [hrewrite, hErase]
              simp
    have hAlphaSubset : Function.mulSupport α ⊆ (S.Sf : Set (FinPlace F)) := by
      intro v hv
      by_contra hnot
      have hmul : α v ≠ 1 := by
        simpa only [Function.mulSupport, Set.mem_setOf_eq] using hv
      have hval : α v = 1 := by
        by_cases hmem : v ∈ S.Sf
        · exact (hnot hmem).elim
        · simp [α, hmem]
      exact hmul hval
    have hAlphaFinite : (Function.mulSupport α).Finite :=
      S.Sf.finite_toSet.subset hAlphaSubset
    have hAlphaProd : (∏ᶠ v, α v) = 1 := by
      rw [finprod_eq_prod_of_mulSupport_subset α hAlphaSubset]
      exact hAlphaFin
    let z₀ : P.RP := P.incl v₀ ((P.loc v₀).z ξ)
    have hFrel : ∀ v, P.compF v zRP = (P.loc v).z (α v) * P.compF v z₀ := by
      intro v
      by_cases hv : v ∈ S.Sf
      · by_cases hv₀ : v = v₀
        · subst v
          have hz : P.compF v₀ zRP = (P.loc v₀).z (phase ⟨v₀, hv₀S⟩) := by
            simpa [hv₀S] using hF v₀
          have hz₀ : P.compF v₀ z₀ = (P.loc v₀).z ξ :=
            P.incl_compF v₀ ((P.loc v₀).z ξ)
          have hmul : (P.loc v₀).z (phase ⟨v₀, hv₀S⟩) =
              (P.loc v₀).z (phase ⟨v₀, hv₀S⟩ / ξ) * (P.loc v₀).z ξ := by
            rw [map_div]
            exact (div_mul_cancel _ _).symm
          calc
            P.compF v₀ zRP = (P.loc v₀).z (phase ⟨v₀, hv₀S⟩) := hz
            _ = (P.loc v₀).z (phase ⟨v₀, hv₀S⟩ / ξ) * (P.loc v₀).z ξ := hmul
            _ = (P.loc v₀).z (α v₀) * P.compF v₀ z₀ := by
              simp [α, b, hv₀S, hz₀]
        · have hz : P.compF v zRP = (P.loc v).z (phase ⟨v, hv⟩) := by
            simpa [hv] using hF v
          have hv₀ne : v₀ ≠ v := Ne.symm hv₀
          have hz₀ : P.compF v z₀ = 1 :=
            P.incl_compF_other v₀ v hv₀ne ((P.loc v₀).z ξ)
          calc
            P.compF v zRP = (P.loc v).z (phase ⟨v, hv⟩) := hz
            _ = (P.loc v).z (α v) * P.compF v z₀ := by
              simp [α, b, hv, hv₀, hz₀]
      · have hz : P.compF v zRP = 1 := by simpa [hv] using hF v
        have hv₀ne : v₀ ≠ v := by
          intro hh
          exact hv (hh ▸ hv₀S)
        have hz₀ : P.compF v z₀ = 1 :=
          P.incl_compF_other v₀ v hv₀ne ((P.loc v₀).z ξ)
        simpa [α, b, hv, hz₀] using hz
    have hCrel : ∀ w, P.compC w zRP = P.compC w z₀ := by
      intro w
      rw [hC w, P.incl_compC]
    have hq := (P.q_eq zRP z₀).2
      ⟨α, hAlphaFinite, hAlphaProd, hFrel, hCrel⟩
    refine ⟨ξ, ?_⟩
    calc
      P.q zRP = P.q z₀ := hq
      _ = P.tc.z ξ := by
        dsimp [z₀]
        rw [P.q_incl, P.emb_z]
  · have hsempty : S.Sf = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hzRP : zRP = 1 := by
      apply P.comp_ext
      · intro v
        rw [hF v]
        simp [hsempty]
      · intro w
        rw [hC w]
        simp
    exact ⟨1, by simp [hzRP]⟩

theorem thetaNormalizationRPFactorization {P : CoverPackage D S H A} (r : P.RP) :
    ∃ (ξ : rootsOfUnity 3 ℂ) (s tail : P.RP) (T : Finset (FinPlace F)),
      P.q s ∈ P.tc.GS ∧
      (∀ v (hv : v ∉ S.Sf), P.compF v s = 1) ∧
      (∀ v ∈ T, v ∉ S.Sf) ∧
      (∀ v (hv : v ∉ S.Sf), P.compF v tail ∈ (P.tame v hv).Kmax) ∧
      (∀ v : S.Sf, P.compF v.1 tail = 1) ∧
      (∀ w, P.compC w tail = 1) ∧
      P.q r = P.tc.z ξ *
        (P.q s * (T.toList.map (fun v => P.emb v (P.compF v r))).prod * P.q tail) := by
  classical
  obtain ⟨s, hsGS, hsProj, hsC, hsExt⟩ := thetaNormalization_supportedRP (P := P) r
  obtain ⟨T, tail, hTout, hTailK, hTailS, hTailT, hTailC, hTailExact⟩ :=
    thetaNormalization_tameTail P r
  let phase : S.Sf → rootsOfUnity 3 ℂ := fun v =>
    Classical.choose (thetaNormalization_supportedCentralPhase (P := P) r s hsProj v)
  have hphase (v : S.Sf) :
      P.compF v.1 r = (P.loc v.1).z (phase v) * P.compF v.1 s :=
    Classical.choose_spec (thetaNormalization_supportedCentralPhase (P := P) r s hsProj v)
  let lf : ∀ v : FinPlace F, (P.loc v).L := fun v =>
    if hv : v ∈ S.Sf then (P.loc v).z (phase ⟨v, hv⟩) else 1
  have hlf_restricted : Set.Finite {v : FinPlace F | ∃ hv : v ∉ S.Sf,
      lf v ∉ (P.tame v hv).Kmax} := by
    apply Set.finite_empty.subset
    intro v hvbad
    rcases hvbad with ⟨hv, hnot⟩
    have hval : lf v = 1 := by simp [lf, hv]
    exact hnot (hval ▸ (P.tame v hv).Kmax.one_mem)
  obtain ⟨centerRP, hcenterF, hcenterC⟩ := P.comp_surj lf (fun _ => 1) hlf_restricted
  obtain ⟨ξ, hcenterQ⟩ := thetaNormalization_centerLift_q (P := P) phase centerRP
    (by intro v; simpa [lf] using hcenterF v) hcenterC
  let extRP := normSExteriorProductRP P r T
  have hRP : r = centerRP * (s * (extRP * tail)) := by
    apply P.comp_ext
    · intro v
      by_cases hvS : v ∈ S.Sf
      · let vS : S.Sf := ⟨v, hvS⟩
        have hnotT : v ∉ T := by
          intro hvT
          exact (hTout v hvT) hvS
        have hcenter : P.compF v centerRP = (P.loc v).z (phase vS) := by
          simpa [lf, hvS] using hcenterF v
        have hprod : P.compF v extRP = 1 := by
          rw [normSExteriorProductRP_compF]
          simp [hnotT]
        have htail : P.compF v tail = 1 := hTailS vS
        calc
          P.compF v r = (P.loc v).z (phase vS) * P.compF v s := hphase vS
          _ = P.compF v centerRP *
              (P.compF v s * (P.compF v extRP * P.compF v tail)) := by
                rw [hcenter, hprod, htail]
                simp
          _ = P.compF v (centerRP * (s * (extRP * tail))) := by
                simp [map_mul, mul_assoc]
      · have hcenter : P.compF v centerRP = 1 := by
          simpa [lf, hvS] using hcenterF v
        have hs : P.compF v s = 1 := hsExt v hvS
        by_cases hvT : v ∈ T
        · have hprod : P.compF v extRP = P.compF v r := by
            rw [normSExteriorProductRP_compF]
            simp [hvT]
          have htail : P.compF v tail = 1 := hTailT v hvT
          calc
            P.compF v r = P.compF v centerRP *
                (P.compF v s * (P.compF v extRP * P.compF v tail)) := by
                  rw [hcenter, hs, hprod, htail]
                  simp
            _ = P.compF v (centerRP * (s * (extRP * tail))) := by
                  simp [map_mul, mul_assoc]
        · have hprod : P.compF v extRP = 1 := by
            rw [normSExteriorProductRP_compF]
            simp [hvT]
          have htail : P.compF v tail = P.compF v r := hTailExact v hvS hvT
          calc
            P.compF v r = P.compF v centerRP *
                (P.compF v s * (P.compF v extRP * P.compF v tail)) := by
                  rw [hcenter, hs, hprod, htail]
                  simp
            _ = P.compF v (centerRP * (s * (extRP * tail))) := by
                  simp [map_mul, mul_assoc]
    · intro w
      have hs := hsC w
      have hprod := normSExteriorProductRP_compC P r T w
      have htail := hTailC w
      have hcenter : P.compC w centerRP = 1 := hcenterC w
      calc
        P.compC w r = P.compC w centerRP *
            (P.compC w s * (P.compC w extRP * P.compC w tail)) := by
              rw [hcenter, hs, hprod, htail]
              simp
        _ = P.compC w (centerRP * (s * (extRP * tail))) := by
              simp [map_mul, mul_assoc]
  have hq : P.q r = P.tc.z ξ *
      (P.q s * (T.toList.map (fun v => P.emb v (P.compF v r))).prod * P.q tail) := by
    calc
      P.q r = P.q (centerRP * (s * (extRP * tail))) := congrArg P.q hRP
      _ = P.q centerRP * (P.q s * (P.q extRP * P.q tail)) := by
        simp [map_mul, mul_assoc]
      _ = P.tc.z ξ *
          (P.q s * (T.toList.map (fun v => P.emb v (P.compF v r))).prod * P.q tail) := by
        rw [hcenterQ, normSExteriorProductRP_q]
        group
  exact ⟨ξ, s, tail, T, hsGS, hsExt, hTout, hTailK, hTailS, hTailC, hq⟩

end ArtinPrimitiveRoots.A1.Theta
