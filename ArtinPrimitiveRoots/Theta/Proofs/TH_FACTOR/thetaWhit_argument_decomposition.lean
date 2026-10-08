import ArtinPrimitiveRoots.Theta.Proofs.TH_FACTOR.Defs

set_option autoImplicit false

open NumberField IsDedekindDomain Filter Topology
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.Theta

open ArtinPrimitiveRoots.A1

variable {F : Type} [Field F] [NumberField F]
variable {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)} {S : SData F CE condη}
  {H : HilbertData F} {A : AddCharData F}

local instance residueMaximalLocal (v : FinPlace F) : v.asIdeal.IsMaximal := v.isMaximal
local instance residueFieldLocal (v : FinPlace F) : Field (𝓞 F ⧸ v.asIdeal) :=
  Ideal.Quotient.field v.asIdeal

private theorem list_mul_prod_commute {α G : Type} [Group G] (x : G) (l : List α)
    (f : α → G) (h : ∀ a ∈ l, x * f a = f a * x) :
    x * (l.map f).prod = (l.map f).prod * x := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha := h a (by simp)
      have ht : ∀ b ∈ l, x * f b = f b * x := by
        intro b hb
        exact h b (by simp [hb])
      simp only [List.map_cons, List.prod_cons]
      calc
        x * (f a * (l.map f).prod) = (x * f a) * (l.map f).prod := by simp [mul_assoc]
        _ = (f a * x) * (l.map f).prod := by rw [ha]
        _ = f a * (x * (l.map f).prod) := by simp [mul_assoc]
        _ = f a * ((l.map f).prod * x) := by rw [ih ht]
        _ = (f a * (l.map f).prod) * x := by simp [mul_assoc]

private theorem list_prod_mul_distribute {α G : Type} [Group G] (l : List α)
    (f g : α → G) (hn : l.Nodup)
    (hcomm : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → f a * g b = g b * f a) :
    (l.map fun a => f a * g a).prod = (l.map f).prod * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      have hcomm' : ∀ x ∈ l, ∀ y ∈ l, x ≠ y → f x * g y = g y * f x := by
        intro x hx y hy hxy
        exact hcomm x (by simp [hx]) y (by simp [hy]) hxy
      have hga : g a * (l.map f).prod = (l.map f).prod * g a := by
        apply list_mul_prod_commute
        intro b hb
        have hba : b ≠ a := by
          intro hab
          subst b
          exact hnot hb
        exact (hcomm b (by simp [hb]) a (by simp) hba).symm
      simp only [List.map_cons, List.prod_cons]
      rw [ih hnodup hcomm']
      calc
        (f a * g a) * ((l.map f).prod * (l.map g).prod) =
            f a * (g a * (l.map f).prod) * (l.map g).prod := by simp [mul_assoc]
        _ = f a * ((l.map f).prod * g a) * (l.map g).prod := by rw [hga]
        _ = (f a * (l.map f).prod) * (g a * (l.map g).prod) := by simp [mul_assoc]

private theorem list_prod_triple_distribute {α G : Type} [Group G] (l : List α)
    (f g h : α → G) (hn : l.Nodup)
    (hfg : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → f a * g b = g b * f a)
    (hfh : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → f a * h b = h b * f a)
    (hgh : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → g a * h b = h b * g a) :
    (l.map fun a => (f a * g a) * h a).prod =
      (l.map f).prod * (l.map g).prod * (l.map h).prod := by
  have hpair : ∀ a ∈ l, ∀ b ∈ l, a ≠ b →
      (f a * g a) * h b = h b * (f a * g a) := by
    intro a ha b hb hab
    calc
      (f a * g a) * h b = f a * (g a * h b) := by simp [mul_assoc]
      _ = f a * (h b * g a) := by rw [hgh a ha b hb hab]
      _ = (h b * f a) * g a := by rw [← hfh a ha b hb hab]; simp [mul_assoc]
      _ = h b * (f a * g a) := by simp [mul_assoc]
  calc
    (l.map fun a => (f a * g a) * h a).prod =
        (l.map fun a => f a * g a).prod * (l.map h).prod :=
          list_prod_mul_distribute l (fun a => f a * g a) h hn hpair
    _ = ((l.map f).prod * (l.map g).prod) * (l.map h).prod := by
          rw [list_prod_mul_distribute l f g hn hfg]

private theorem list_prod_map_eq_of_comm_of_toFinset_eq {α G : Type} [Group G]
    [DecidableEq α] (l₁ l₂ : List α) (f : α → G)
    (hfin : l₁.toFinset = l₂.toFinset)
    (hcomm₁ : ∀ a ∈ l₁, ∀ b ∈ l₁, a ≠ b → f a * f b = f b * f a)
    (hcomm₂ : ∀ a ∈ l₂, ∀ b ∈ l₂, a ≠ b → f a * f b = f b * f a)
    (hn₁ : l₁.Nodup) (hn₂ : l₂.Nodup) :
    (l₁.map f).prod = (l₂.map f).prod := by
  let comm₁ : (↑l₁.toFinset : Set α).Pairwise (Function.onFun Commute f) := by
    intro a ha b hb hab
    by_cases hab : a = b
    · subst b
      exact Commute.refl (f a)
    · exact hcomm₁ a (by simpa using ha) b (by simpa using hb) hab
  let comm₂ : (↑l₂.toFinset : Set α).Pairwise (Function.onFun Commute f) := by
    intro a ha b hb hab
    by_cases hab : a = b
    · subst b
      exact Commute.refl (f a)
    · exact hcomm₂ a (by simpa using ha) b (by simpa using hb) hab
  calc
    (l₁.map f).prod = l₁.toFinset.noncommProd f comm₁ :=
      (Finset.noncommProd_toFinset l₁ f comm₁ hn₁).symm
    _ = l₂.toFinset.noncommProd f comm₂ := by
      exact Finset.noncommProd_congr hfin (fun _ _ => rfl) comm₁
    _ = (l₂.map f).prod := Finset.noncommProd_toFinset l₂ f comm₂ hn₂

private theorem list_prod_if_eq_filter {α G : Type} [Monoid G] (l : List α)
    (p : α → Prop) [DecidablePred p] (f : α → G) :
    (l.map fun a => if p a then f a else 1).prod =
      ((l.filter fun a => decide (p a)).map f).prod := by
  induction l with
  | nil => simp
  | cons a l ih => by_cases hp : p a <;> simp [hp, ih]

private theorem mul_swap_middle {G : Type} [Group G] (a b c d : G)
    (h : b * c = c * b) : a * b * c * d = a * c * b * d := by
  calc
    a * b * c * d = a * (b * c) * d := by simp [mul_assoc]
    _ = a * (c * b) * d := by rw [h]
    _ = a * c * b * d := by simp [mul_assoc]

private theorem comp_incl_prod {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)}
    {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (l : List (FinPlace F))
    (f : ∀ v, (P.loc v).L) (hn : l.Nodup) (v : FinPlace F) :
    P.compF v ((l.map fun v' => P.incl v' (f v')).prod) =
      if v ∈ l then f v else 1 := by
  induction l with
  | nil => simp
  | cons v₀ l ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rw [List.map_cons, List.prod_cons, (P.compF v).map_mul]
      by_cases hv : v = v₀
      · subst v₀
        rw [P.incl_compF]
        have htail := ih hnodup
        have htail' : P.compF v ((l.map fun v' => P.incl v' (f v')).prod) = 1 := by
          simpa [hnot] using htail
        simp [hnot, htail']
      · have hfirst : P.compF v (P.incl v₀ (f v₀)) = 1 := by
          exact P.incl_compF_other v₀ v (Ne.symm hv) (f v₀)
        rw [hfirst]
        simp [hv, ih hnodup]

private theorem compC_incl_prod {D : FieldData F} {CE : ℕ} {condη : Ideal (𝓞 F)}
    {S : SData F CE condη} {H : HilbertData F} {A : AddCharData F}
    (P : CoverPackage D S H A) (l : List (FinPlace F))
    (f : ∀ v, (P.loc v).L) (w : InfinitePlace F) :
    P.compC w ((l.map fun v => P.incl v (f v)).prod) = 1 := by
  induction l with
  | nil => simp
  | cons v l ih =>
      simp [List.map_cons, List.prod_cons, (P.compC w).map_mul, P.incl_compC, ih]

private theorem residue_rep_local (v : FinPlace F) (x : F) (a b : 𝓞 F)
    (hb : b ∉ v.asIdeal) (hab : x * algebraMap (𝓞 F) F b = algebraMap (𝓞 F) F a) :
    residue v x = Ideal.Quotient.mk v.asIdeal a / Ideal.Quotient.mk v.asIdeal b := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hex : ∃ ab : 𝓞 F × 𝓞 F, ab.2 ∉ v.asIdeal ∧
      x * algebraMap (𝓞 F) F ab.2 = algebraMap (𝓞 F) F ab.1 := ⟨(a, b), hb, hab⟩
  have hcross : hex.choose.1 * b = a * hex.choose.2 := by
    apply (IsFractionRing.injective (𝓞 F) F)
    simp only [map_mul]
    rw [← hex.choose_spec.2, ← hab]
    ring
  have hqcross := congrArg (Ideal.Quotient.mk v.asIdeal) hcross
  have hbq : Ideal.Quotient.mk v.asIdeal b ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hb
  have hdq : Ideal.Quotient.mk v.asIdeal hex.choose.2 ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hex.choose_spec.1
  unfold residue
  rw [dif_pos hex]
  rw [← div_eq_mul_inv, div_eq_div_iff hdq hbq]
  simpa only [map_mul] using hqcross

private theorem residue_ne_zero_local (v : FinPlace F) (x : F)
    (hx : HeightOneSpectrum.valuation F v x ≤ 1) :
    residue v x ≠ 0 ↔ HeightOneSpectrum.valuation F v x = 1 := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  obtain ⟨a, b, hab⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
  have hbval : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F b.val) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F) (r := b.val)).2 b.property
  have hval : HeightOneSpectrum.valuation F v x =
      HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F a) := by
    have := congrArg (HeightOneSpectrum.valuation F v) hab
    simpa only [map_mul, hbval, mul_one] using this
  rw [residue_rep_local v _ _ _ b.property hab, div_ne_zero_iff, hval,
    v.valuation_eq_one_iff_notMem (K := F) (r := a)]
  have hb : b.val ∉ v.asIdeal := b.property
  simp only [ne_eq, Ideal.Quotient.eq_zero_iff_mem, hb, not_false_eq_true, and_true]

private theorem valuation_le_one_of_residue_ne_zero (v : FinPlace F) (x : F)
    (hx : residue v x ≠ 0) : HeightOneSpectrum.valuation F v x ≤ 1 := by
  letI : v.asIdeal.IsMaximal := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hex : ∃ ab : 𝓞 F × 𝓞 F, ab.2 ∉ v.asIdeal ∧
      x * algebraMap (𝓞 F) F ab.2 = algebraMap (𝓞 F) F ab.1 := by
    unfold residue at hx
    split_ifs at hx with h
    · exact h
    · exact False.elim (hx rfl)
  obtain ⟨ab, hb, hab⟩ := hex
  have hbval : HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F ab.2) = 1 :=
    (v.valuation_eq_one_iff_notMem (K := F) (r := ab.2)).2 hb
  have hval : HeightOneSpectrum.valuation F v x =
      HeightOneSpectrum.valuation F v (algebraMap (𝓞 F) F ab.1) := by
    have := congrArg (HeightOneSpectrum.valuation F v) hab
    simpa only [map_mul, hbval, mul_one] using this
  rw [hval]
  exact v.valuation_le_one ab.1

private theorem toLoc_isLocUnit_local (v : FinPlace F) (x : Fˣ)
    (hx : HeightOneSpectrum.valuation F v (x : F) = 1) : IsLocUnit v (toLoc v x) := by
  have hval : Valued.v ((toLoc v x : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    change Valued.v (algebraMap F (v.adicCompletion F) (x : F)) = 1
    simp only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self, RingHom.id_apply, v.valuedAdicCompletion_eq_valuation', hx]
  constructor
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    exact hval.le
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    simp only [Units.val_inv_eq_inv_val, map_inv₀, hval, inv_one, le_refl]

private theorem glMap_diagGL {K : Type} [Field K] (φ : F →+* K) (ν : Fˣ) :
    Matrix.GeneralLinearGroup.map φ (diagGL ν) =
      diagM K (Units.map φ.toMonoidHom ν) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagGL, diagM]

private theorem glMap_weylGL {K : Type} [Field K] (φ : F →+* K) :
    Matrix.GeneralLinearGroup.map φ weylGL = weylM K := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylGL, weylM]

private theorem compU_diagU (v : S.Sf) (ν : Fˣ) :
    S.compU v (S.diagU ν) = toLoc v.1 ν := by
  apply Units.ext
  rfl

private theorem compC_diagU (w : InfinitePlace F) (ν : Fˣ) :
    S.compC w (S.diagU ν) = Units.map w.embedding.toMonoidHom ν := by
  apply Units.ext
  rfl

private theorem aExt_tail_lift {P : CoverPackage D S H A} (ν : Fˣ)
    (U : Finset (FinPlace F)) (hU : ∀ v ∈ U, v ∉ S.Sf)
    (hν : ∀ v : FinPlace F, v ∉ S.Sf → v ∉ U →
      residue v (ν : F) ≠ 0 ∧ residue v ((ν⁻¹ : Fˣ) : F) ≠ 0)
    (k : P.tc.G)
    (hAExt : P.tc.aExt ν = (U.toList.map fun v => P.tc.a v (toLoc v ν)).prod * k) :
    ∃ x : P.RP, P.q x = k ∧
      (∀ v, v ∈ S.Sf → P.compF v x = 1) ∧
      (∀ v (hv : v ∉ S.Sf), P.compF v x ∈ (P.tame v hv).Kmax) ∧
      (∀ w, P.compC w x = 1) := by
  classical
  obtain ⟨xS, hxSq, hxScomp, hxSc⟩ := P.aS_components (S.diagU ν)
  let xA : P.RP := (U.toList.map fun v => P.incl v ((P.loc v).a (toLoc v ν))).prod
  let Aprod : P.tc.G := (U.toList.map fun v => P.tc.a v (toLoc v ν)).prod
  have hxAq : P.q xA = Aprod := by
    rw [map_list_prod]
    rw [List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro v hv
    simp only [Function.comp_apply]
    rw [P.q_incl, P.emb_a v (hU v (Finset.mem_toList.mp hv))]
  have hxAcomp : ∀ v, P.compF v xA =
      if v ∈ U then (P.loc v).a (toLoc v ν) else 1 := by
    intro v
    simpa [xA, Finset.mem_toList] using
      (comp_incl_prod P U.toList (fun v => (P.loc v).a (toLoc v ν))
        (Finset.nodup_toList U) v)
  have hxAc : ∀ w, P.compC w xA = 1 := by
    intro w
    exact compC_incl_prod P U.toList (fun v => (P.loc v).a (toLoc v ν)) w
  let xR : P.RP := P.ratRP (diagGL ν)
  have hxRq : P.q xR = P.tc.rat (diagGL ν) := P.q_ratRP _
  have hxRcomp : ∀ v, P.compF v xR = (P.loc v).a (toLoc v ν) := by
    intro v
    rw [P.compF_ratRP, glMap_diagGL, (P.loc v).sec_a]
    simp [toLoc]
  have hxRc : ∀ w, P.compC w xR =
      QuotientGroup.mk (diagM ℂ (Units.map w.embedding.toMonoidHom ν)) := by
    intro w
    rw [P.compC_ratRP, glMap_diagGL]
  let x : P.RP := xA⁻¹ * xS⁻¹ * xR
  have hxq : P.q x = k := by
    have hq : P.q x = Aprod⁻¹ * (P.tc.aS (S.diagU ν))⁻¹ * P.tc.rat (diagGL ν) := by
      simp [x, P.q.map_mul, hxAq, hxSq, hxRq]
    rw [hq, P.tc.rat_diag ν, hAExt]
    simp [Aprod, mul_assoc]
  refine ⟨x, hxq, ?_, ?_, ?_⟩
  · intro v hvS
    have hvU : v ∉ U := by
      intro hvU
      exact (hU v hvU) hvS
    have hcompX : P.compF v x =
        (P.compF v xA)⁻¹ * (P.compF v xS)⁻¹ * P.compF v xR := by
      simp [x, (P.compF v).map_mul, (P.compF v).map_inv]
    have hSdiag : P.compF v xS = (P.loc v).a (toLoc v ν) := by
      rw [hxScomp v]
      simp [hvS]
      rw [compU_diagU]
    rw [hcompX, hxAcomp v, if_neg hvU, hSdiag, hxRcomp v]
    simp
  · intro v hvS
    by_cases hvU : v ∈ U
    · have hcompX : P.compF v x =
          (P.compF v xA)⁻¹ * (P.compF v xS)⁻¹ * P.compF v xR := by
        simp [x, (P.compF v).map_mul, (P.compF v).map_inv]
      have hSdiag : P.compF v xS = 1 := by rw [hxScomp v]; simp [hvS]
      rw [hcompX, hxAcomp v, if_pos hvU, hSdiag, hxRcomp v]
      simp
    · have hcompX : P.compF v x =
          (P.compF v xA)⁻¹ * (P.compF v xS)⁻¹ * P.compF v xR := by
        simp [x, (P.compF v).map_mul, (P.compF v).map_inv]
      have hSdiag : P.compF v xS = 1 := by rw [hxScomp v]; simp [hvS]
      have hunit : IsLocUnit v (toLoc v ν) := by
        apply toLoc_isLocUnit_local
        exact (residue_ne_zero_local v (ν : F)
          (valuation_le_one_of_residue_ne_zero v (ν : F) (hν v hvS hvU).1)).mp
          (hν v hvS hvU).1
      rw [hcompX, hxAcomp v, if_neg hvU, hSdiag, hxRcomp v]
      simpa using (P.tame v hvS).a_mem (toLoc v ν) hunit.1 hunit.2
  · intro w
    have hcompX : P.compC w x =
        (P.compC w xA)⁻¹ * (P.compC w xS)⁻¹ * P.compC w xR := by
      simp [x, (P.compC w).map_mul, (P.compC w).map_inv]
    rw [hcompX, hxAc w, hxSc w, hxRc w, compC_diagU]
    simp

private theorem wExt_tail_lift {P : CoverPackage D S H A}
    (U : Finset (FinPlace F)) (hU : ∀ v ∈ U, v ∉ S.Sf) (k : P.tc.G)
    (hWExt : P.tc.wExt = (U.toList.map P.tc.w).prod * k) :
    ∃ x : P.RP, P.q x = k ∧
      (∀ v, v ∈ S.Sf → P.compF v x = 1) ∧
      (∀ v (hv : v ∉ S.Sf), P.compF v x ∈ (P.tame v hv).Kmax) ∧
      (∀ w, P.compC w x = 1) := by
  classical
  obtain ⟨xS, hxSq, hxScomp, hxSc⟩ := P.wS_components
  let xW : P.RP := (U.toList.map fun v => P.incl v (P.loc v).w).prod
  let Wprod : P.tc.G := (U.toList.map P.tc.w).prod
  have hxWq : P.q xW = Wprod := by
    rw [map_list_prod]
    rw [List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro v hv
    simp only [Function.comp_apply]
    rw [P.q_incl, P.emb_w v (hU v (Finset.mem_toList.mp hv))]
  have hxWcomp : ∀ v, P.compF v xW =
      if v ∈ U then (P.loc v).w else 1 := by
    intro v
    simpa [xW, Finset.mem_toList] using
      (comp_incl_prod P U.toList (fun v => (P.loc v).w) (Finset.nodup_toList U) v)
  have hxWc : ∀ w, P.compC w xW = 1 := by
    intro w
    exact compC_incl_prod P U.toList (fun v => (P.loc v).w) w
  let xR : P.RP := P.ratRP weylGL
  have hxRq : P.q xR = P.tc.rat weylGL := P.q_ratRP _
  have hxRcomp : ∀ v, P.compF v xR = (P.loc v).w := by
    intro v
    rw [P.compF_ratRP, glMap_weylGL, ← (P.loc v).sec_w]
  have hxRc : ∀ w, P.compC w xR = QuotientGroup.mk (weylM ℂ) := by
    intro w
    rw [P.compC_ratRP, glMap_weylGL]
  let x : P.RP := xW⁻¹ * xS⁻¹ * xR
  have hxq : P.q x = k := by
    have hq : P.q x = Wprod⁻¹ * (P.tc.wS)⁻¹ * P.tc.rat weylGL := by
      simp [x, P.q.map_mul, hxWq, hxSq, hxRq]
    rw [hq, P.tc.rat_weyl, hWExt]
    simp [Wprod, mul_assoc]
  refine ⟨x, hxq, ?_, ?_, ?_⟩
  · intro v hvS
    have hvU : v ∉ U := by
      intro hvU
      exact (hU v hvU) hvS
    have hcompX : P.compF v x =
        (P.compF v xW)⁻¹ * (P.compF v xS)⁻¹ * P.compF v xR := by
      simp [x, (P.compF v).map_mul, (P.compF v).map_inv]
    have hS_w : P.compF v xS = (P.loc v).w := by
      rw [hxScomp v]
      simp [hvS]
    rw [hcompX, hxWcomp v, if_neg hvU, hS_w, hxRcomp v]
    simp
  · intro v hvS
    by_cases hvU : v ∈ U
    · have hcompX : P.compF v x =
          (P.compF v xW)⁻¹ * (P.compF v xS)⁻¹ * P.compF v xR := by
        simp [x, (P.compF v).map_mul, (P.compF v).map_inv]
      have hS_w : P.compF v xS = 1 := by rw [hxScomp v]; simp [hvS]
      rw [hcompX, hxWcomp v, if_pos hvU, hS_w, hxRcomp v]
      simp
    · have hcompX : P.compF v x =
          (P.compF v xW)⁻¹ * (P.compF v xS)⁻¹ * P.compF v xR := by
        simp [x, (P.compF v).map_mul, (P.compF v).map_inv]
      have hS_w : P.compF v xS = 1 := by rw [hxScomp v]; simp [hvS]
      rw [hcompX, hxWcomp v, if_neg hvU, hS_w, hxRcomp v]
      simpa using (P.tame v hvS).w_mem
  · intro w
    have hcompX : P.compC w x =
        (P.compC w xW)⁻¹ * (P.compC w xS)⁻¹ * P.compC w xR := by
      simp [x, (P.compC w).map_mul, (P.compC w).map_inv]
    rw [hcompX, hxWc w, hxSc w, hxRc w]
    simp

private theorem scalarOf_right_of_components {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (hT : Fam.T0 = S.Sf) (k : P.tc.G) (x : P.RP) (hxq : P.q x = k)
    (hxS : ∀ v, v ∈ S.Sf → P.compF v x = 1)
    (hxExt : ∀ v (hv : v ∉ S.Sf), P.compF v x ∈ (P.tame v hv).Kmax)
    (hxC : ∀ w, P.compC w x = 1) :
    ∀ s h, scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * k) =
      scalarOf P G (Fam.sec s).f (Fam.sec s).fC h := by
  intro s h
  let y := Function.surjInv P.q_surj h
  have hy : P.q y = h := Function.surjInv_eq P.q_surj h
  have hyx : P.q (y * x) = h * k := by
    rw [P.q.map_mul, hy, hxq]
  have hf : ∀ v, (Fam.sec s).f v (P.compF v (y * x)) =
      (Fam.sec s).f v (P.compF v y) := by
    intro v
    have hcomp : P.compF v (y * x) = P.compF v y * P.compF v x :=
      (P.compF v).map_mul y x
    rw [hcomp]
    by_cases hvS : v ∈ S.Sf
    · rw [hxS v hvS]
      simp
    · have hvT0 : v ∉ (Fam.sec s).T0 := by
        intro hmem
        have hmem' : v ∈ Fam.T0 := by
          rw [← Fam.T0_eq s]
          exact hmem
        have hmemS : v ∈ S.Sf := by
          rw [← hT]
          exact hmem'
        exact hvS hmemS
      exact ((Fam.sec s).f_sph v hvT0).2 (P.compF v y) (P.compF v x) (hxExt v hvS)
  have hc : ∀ w, P.compC w (y * x) = P.compC w y := by
    intro w
    rw [(P.compC w).map_mul, hxC w]
    simp
  have hfinite :
      (∏ᶠ v, G.lam v ((Fam.sec s).f v (P.compF v (y * x)))) =
        ∏ᶠ v, G.lam v ((Fam.sec s).f v (P.compF v y)) := by
    apply finprod_congr
    intro v
    rw [hf v]
  have hcomplex :
      (∏ w, (Fam.sec s).fC w (P.compC w (y * x))) =
        ∏ w, (Fam.sec s).fC w (P.compC w y) := by
    apply Finset.prod_congr rfl
    intro w hw
    rw [hc w]
  have hformula :
        (∏ᶠ v, G.lam v ((Fam.sec s).f v (P.compF v (y * x)))) *
          ∏ w, (Fam.sec s).fC w (P.compC w (y * x)) =
        (∏ᶠ v, G.lam v ((Fam.sec s).f v (P.compF v y))) *
          ∏ w, (Fam.sec s).fC w (P.compC w y) := by
    rw [hfinite, hcomplex]
  have hsx := (scalarOf_q P G (Fam.sec s) (y * x)).2
  have hs := (scalarOf_q P G (Fam.sec s) y).2
  rw [hyx] at hsx
  rw [hy] at hs
  rw [hsx, hs]
  exact hformula

theorem theta_right_of_scalar_fix {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (C : ContinuedEis Fam) (k : P.tc.G)
    (hfix : ∀ s h, scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * k) =
      scalarOf P G (Fam.sec s).f (Fam.sec s).fC h) :
    ∀ g, C.theta (g * k) = C.theta g := by
  intro g
  let U := ArtinPrimitiveRoots.A1.Spec.contDomain (1 / 6) C.ε
  have hFanal : AnalyticOnNhd ℂ (fun s => (s - (1 / 6 : ℂ)) * C.E s (g * k)) U := by
    exact (analyticOnNhd_id.sub analyticOnNhd_const).mul (C.E_analytic (g * k))
  have hGanal : AnalyticOnNhd ℂ (fun s => (s - (1 / 6 : ℂ)) * C.E s g) U := by
    exact (analyticOnNhd_id.sub analyticOnNhd_const).mul (C.E_analytic g)
  have hbase : ∀ s ∈ Metric.ball (5 / 2 : ℂ) (1 / 2),
      (s - (1 / 6 : ℂ)) * C.E s (g * k) = (s - (1 / 6 : ℂ)) * C.E s g := by
    intro s hs
    have hdist : dist s (5 / 2 : ℂ) < (1 / 2 : ℝ) := Metric.mem_ball.mp hs
    have hnorm : ‖s - (5 / 2 : ℂ)‖ < (1 / 2 : ℝ) := by
      simpa [dist_eq_norm] using hdist
    have hreal : (1 / 2 : ℝ) < s.re := by
      have hrealAbs : |s.re - (5 / 2 : ℝ)| ≤ ‖s - (5 / 2 : ℂ)‖ := by
        simpa using Complex.abs_re_le_norm (s - (5 / 2 : ℂ))
      have hlow := (abs_lt.mp (lt_of_le_of_lt hrealAbs hnorm)).1
      linarith
    have hauto := eisenstein_automorphic P G hreal (Fam.sec s)
    have heis : C.E s (g * k) = C.E s g := by
      calc
        C.E s (g * k) = eisenstein P G (Fam.sec s) (g * k) := C.E_series s hs (g * k)
        _ = eisenstein P G (Fam.sec s) g := hauto.2.2 k (hfix s) g
        _ = C.E s g := (C.E_series s hs g).symm
    rw [heis]
  have hcenter : (5 / 2 : ℂ) ∈ U := by
    dsimp [U, ArtinPrimitiveRoots.A1.Spec.contDomain]
    exact Or.inl (Or.inr (Metric.mem_ball_self (by norm_num : (0 : ℝ) < (1 / 2 : ℝ))))
  have hbaseNear :
      (fun s => (s - (1 / 6 : ℂ)) * C.E s (g * k)) =ᶠ[𝓝 (5 / 2 : ℂ)]
        (fun s => (s - (1 / 6 : ℂ)) * C.E s g) := by
    filter_upwards [Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < (1 / 2 : ℝ))]
      with s hs
    exact hbase s hs
  have hreg : Set.EqOn (fun s => (s - (1 / 6 : ℂ)) * C.E s (g * k))
      (fun s => (s - (1 / 6 : ℂ)) * C.E s g) U :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hFanal hGanal
      (ArtinPrimitiveRoots.A1.Spec.isPreconnected_contDomain (1 / 6) C.ε
        (by norm_num) (by norm_num) C.ε_pos) hcenter hbaseNear
  rcases C.laurent (g * k) with ⟨Ψ₁, hΨ₁anal, hΨ₁center, hΨ₁eq⟩
  rcases C.laurent g with ⟨Ψ₂, hΨ₂anal, hΨ₂center, hΨ₂eq⟩
  let B := Metric.ball (1 / 6 : ℂ) C.ε
  have hΨeq : ∀ s, s ∈ B \ {(1 / 6 : ℂ)} → Ψ₁ s = Ψ₂ s := by
    intro s hs
    change s ∈ Metric.ball (1 / 6 : ℂ) C.ε \ {(1 / 6 : ℂ)} at hs
    have hsU : s ∈ U := by
      dsimp [U, ArtinPrimitiveRoots.A1.Spec.contDomain]
      have hc : (1 / 6 : ℂ) = ((1 / 6 : ℝ) : ℂ) := by norm_num
      rw [hc] at hs
      exact Or.inr hs
    have hregS := hreg hsU
    have hneq : s ≠ (1 / 6 : ℂ) := by simpa using hs.2
    rw [hΨ₁eq s hs.1 hneq, hΨ₂eq s hs.1 hneq]
    exact hregS
  let z₀ : ℂ := (1 / 6 : ℂ) + (C.ε / 2 : ℂ)
  have hz₀ball : z₀ ∈ B := by
    apply Metric.mem_ball.mpr
    dsimp [z₀, B]
    rw [dist_eq_norm, add_sub_cancel_left]
    have hεHalf : 0 < C.ε / 2 := half_pos C.ε_pos
    calc
      ‖(C.ε : ℂ) / 2‖ = ‖(C.ε : ℂ)‖ / ‖(2 : ℂ)‖ := norm_div _ _
      _ = C.ε / 2 := by simp [Complex.norm_real, abs_of_pos C.ε_pos]
      _ < C.ε := by linarith [C.ε_pos]
  have hz₀ne : z₀ ≠ (1 / 6 : ℂ) := by
    intro h
    have hεC : (C.ε / 2 : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (div_pos C.ε_pos (by norm_num : (0 : ℝ) < 2)))
    apply hεC
    calc
      (C.ε / 2 : ℂ) = z₀ - (1 / 6 : ℂ) := by dsimp [z₀]; ring
      _ = 0 := by rw [h]; simp
  have hBOpen : IsOpen B := by dsimp [B]; exact Metric.isOpen_ball
  have hpunctOpen : IsOpen (B \ {(1 / 6 : ℂ)}) :=
    IsOpen.sdiff hBOpen isClosed_singleton
  have hnearPunct : B \ {(1 / 6 : ℂ)} ∈ 𝓝 z₀ :=
    hpunctOpen.mem_nhds ⟨hz₀ball, by simpa using hz₀ne⟩
  have hΨnear : Ψ₁ =ᶠ[𝓝 z₀] Ψ₂ := by
    filter_upwards [hnearPunct] with s hs
    exact hΨeq s hs
  have hΨonBall : Set.EqOn Ψ₁ Ψ₂ B :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hΨ₁anal hΨ₂anal
      Metric.isPreconnected_ball hz₀ball hΨnear
  have hs₀ball : (1 / 6 : ℂ) ∈ B := by
    dsimp [B]
    exact Metric.mem_ball_self C.ε_pos
  have hθ := hΨonBall hs₀ball
  rw [hΨ₁center, hΨ₂center] at hθ
  exact hθ

/-- Decompose the frozen factorization argument using the exact Finset.toList order.
The tail is also certified to fix the scalar sections of the given family; arbitrary
Kext membership alone is not used to assert this.
Uses frozen `rat_diag`, `rat_weyl`, `aExt_split`, `wExt_split`, cover component
laws, `scalarOf_q`, and exterior sphericity; feeds `thetaWhit_factor_iteration`. -/
theorem thetaWhit_argument_decomposition {P : CoverPackage D S H A} {G : GlobalDatum P}
    {μ : ∀ v : FinPlace F, LocHaar v} (Fam : AnalyticFamily P G μ)
    (hT : Fam.T0 = S.Sf) (ν : Fˣ) (ε : Bool) (gS : P.tc.G) (hgS : gS ∈ P.tc.GS)
    (T U : Finset (FinPlace F)) (hTU : T ⊆ U) (hU : ∀ v ∈ U, v ∉ S.Sf)
    (hν : ∀ v : FinPlace F, v ∉ S.Sf → v ∉ U →
      residue v (ν : F) ≠ 0 ∧ residue v ((ν⁻¹ : Fˣ) : F) ≠ 0)
    (g : FinPlace F → P.tc.G) (hg : ∀ v ∈ T, g v ∈ P.tc.Gloc v) :
    ∃ k ∈ P.tc.Kext, (∀ v ∈ U, ∀ h ∈ P.tc.Gloc v, k * h = h * k) ∧
      P.tc.rat (diagGL ν) * (if ε then P.tc.rat weylGL else 1) * gS *
        (T.toList.map g).prod =
      (P.tc.aS (S.diagU ν) * (if ε then P.tc.wS else 1) * gS) *
        (U.toList.map (thetaWhit_localArgument P ν ε T g)).prod * k ∧
      ∀ s h, scalarOf P G (Fam.sec s).f (Fam.sec s).fC (h * k) =
        scalarOf P G (Fam.sec s).f (Fam.sec s).fC h := by
  classical
  obtain ⟨ka, hkaK, hkaComm, hAExt⟩ := P.tc.aExt_split ν U hU hν
  let aF : FinPlace F → P.tc.G := fun v => P.tc.a v (toLoc v ν)
  let wF : FinPlace F → P.tc.G := fun v => if ε then P.tc.w v else 1
  let gF : FinPlace F → P.tc.G := fun v => if v ∈ T then g v else 1
  let Aprod : P.tc.G := (U.toList.map aF).prod
  let Wprod : P.tc.G := (U.toList.map wF).prod
  let Gprod : P.tc.G := (U.toList.map gF).prod
  have haLoc : ∀ v ∈ U.toList, aF v ∈ P.tc.Gloc v := by
    intro v hv
    exact P.tc.a_mem v (toLoc v ν)
  have hwLoc : ∀ v ∈ U.toList, wF v ∈ P.tc.Gloc v := by
    intro v hv
    by_cases hε : ε
    · simp [wF, hε]
      exact P.tc.w_mem v
    · simp [wF, hε]
  have hgLoc : ∀ v ∈ U.toList, gF v ∈ P.tc.Gloc v := by
    intro v hv
    by_cases hvT : v ∈ T
    · simp [gF, hvT]
      exact hg v hvT
    · simp [gF, hvT]
  have hLocal :
      (U.toList.map (thetaWhit_localArgument P ν ε T g)).prod = Aprod * Wprod * Gprod := by
    change (U.toList.map fun v => (aF v * wF v) * gF v).prod = Aprod * Wprod * Gprod
    apply list_prod_triple_distribute U.toList aF wF gF (Finset.nodup_toList U)
    · intro v hv w hw hvw
      exact P.tc.comm_loc v w hvw (aF v) (haLoc v hv) (wF w) (hwLoc w hw)
    · intro v hv w hw hvw
      exact P.tc.comm_loc v w hvw (aF v) (haLoc v hv) (gF w) (hgLoc w hw)
    · intro v hv w hw hvw
      exact P.tc.comm_loc v w hvw (wF v) (hwLoc v hv) (gF w) (hgLoc w hw)
  have hGprod : Gprod = (T.toList.map g).prod := by
    dsimp only [Gprod, gF]
    rw [list_prod_if_eq_filter]
    let l₁ := U.toList.filter fun v => decide (v ∈ T)
    have hn₁ : l₁.Nodup := (Finset.nodup_toList U).filter _
    have hn₂ : T.toList.Nodup := Finset.nodup_toList T
    have hfin' : l₁.toFinset = T := by
      ext v
      simp [l₁, hTU]
    have hfin : l₁.toFinset = T.toList.toFinset := hfin'.trans (by simp)
    have hcomm₁ : ∀ v ∈ l₁, ∀ w ∈ l₁, v ≠ w → g v * g w = g w * g v := by
      intro v hv w hw hvw
      have hv' : v ∈ U.toList.filter (fun x => decide (x ∈ T)) := by simpa [l₁] using hv
      have hw' : w ∈ U.toList.filter (fun x => decide (x ∈ T)) := by simpa [l₁] using hw
      have hvT : v ∈ T := by
        have hv'' : v ∈ U.toList ∧ v ∈ T := by
          simpa only [List.mem_filter, decide_eq_true_eq] using hv'
        exact hv''.2
      have hwT : w ∈ T := by
        have hw'' : w ∈ U.toList ∧ w ∈ T := by
          simpa only [List.mem_filter, decide_eq_true_eq] using hw'
        exact hw''.2
      exact P.tc.comm_loc v w hvw (g v) (hg v hvT) (g w) (hg w hwT)
    have hcomm₂ : ∀ v ∈ T.toList, ∀ w ∈ T.toList, v ≠ w → g v * g w = g w * g v := by
      intro v hv w hw hvw
      exact P.tc.comm_loc v w hvw (g v) (hg v (Finset.mem_toList.mp hv))
        (g w) (hg w (Finset.mem_toList.mp hw))
    exact list_prod_map_eq_of_comm_of_toFinset_eq l₁ T.toList g hfin hcomm₁ hcomm₂ hn₁ hn₂
  have hA_gS : Aprod * gS = gS * Aprod := by
    have h := list_mul_prod_commute gS U.toList aF (by
      intro v hv
      exact (P.tc.comm_S v (hU v (Finset.mem_toList.mp hv)) (aF v)
        (P.tc.a_mem v (toLoc v ν)) gS hgS).symm)
    exact h.symm
  have hG_gS : Gprod * gS = gS * Gprod := by
    have h := list_mul_prod_commute gS U.toList gF (by
      intro v hv
      exact (P.tc.comm_S v (hU v (Finset.mem_toList.mp hv)) (gF v) (hgLoc v hv) gS hgS).symm)
    exact h.symm
  have hKa_gS : ka * gS = gS * ka := P.tc.Kext_comm_S ka hkaK gS hgS
  have hKa_G : ka * Gprod = Gprod * ka := by
    apply list_mul_prod_commute ka U.toList gF
    intro v hv
    by_cases hvT : v ∈ T
    · simpa [gF, hvT] using hkaComm v (Finset.mem_toList.mp hv) (g v) (hg v hvT)
    · simp [gF, hvT]
  cases ε with
  | false =>
      refine ⟨ka, hkaK, hkaComm, ?_, ?_⟩
      · change P.tc.rat (diagGL ν) * 1 * gS * (T.toList.map g).prod =
          (P.tc.aS (S.diagU ν) * 1 * gS) *
            (U.toList.map (thetaWhit_localArgument P ν false T g)).prod * ka
        rw [P.tc.rat_diag ν, hAExt, ← hGprod]
        simp only [if_false, mul_one]
        have hLocal' :
            (U.toList.map (thetaWhit_localArgument P ν false T g)).prod = Aprod * Gprod := by
          simpa [Wprod, wF] using hLocal
        rw [hLocal']
        calc
          P.tc.aS (S.diagU ν) * (Aprod * ka) * gS * Gprod =
              P.tc.aS (S.diagU ν) * Aprod * ka * gS * Gprod := by simp [mul_assoc]
          _ = P.tc.aS (S.diagU ν) * Aprod * gS * ka * Gprod :=
                mul_swap_middle (P.tc.aS (S.diagU ν) * Aprod) ka gS Gprod hKa_gS
          _ = P.tc.aS (S.diagU ν) * gS * Aprod * ka * Gprod :=
                by
                  simpa [mul_assoc] using congrArg (fun x => x * Gprod)
                    (mul_swap_middle (P.tc.aS (S.diagU ν)) Aprod gS ka hA_gS)
          _ = P.tc.aS (S.diagU ν) * gS * Aprod * Gprod * ka := by
                simpa using mul_swap_middle
                  (P.tc.aS (S.diagU ν) * gS * Aprod) ka Gprod 1 hKa_G
          _ = (P.tc.aS (S.diagU ν) * gS) * (Aprod * Gprod) * ka := by
                simp [mul_assoc]
      · obtain ⟨xka, hxkaq, hxkaS, hxkaExt, hxkaC⟩ :=
          aExt_tail_lift (P := P) ν U hU hν ka hAExt
        exact scalarOf_right_of_components Fam hT ka xka hxkaq hxkaS hxkaExt hxkaC
  | true =>
      obtain ⟨kw, hkwK, hkwComm, hWExt⟩ := P.tc.wExt_split U hU
      refine ⟨ka * kw, P.tc.Kext.mul_mem hkaK hkwK, ?_, ?_, ?_⟩
      · intro v hv h hh
        calc
          (ka * kw) * h = ka * (kw * h) := by simp [mul_assoc]
          _ = ka * (h * kw) := by rw [hkwComm v hv h hh]
          _ = (ka * h) * kw := by simp [mul_assoc]
          _ = (h * ka) * kw := by rw [hkaComm v hv h hh]
          _ = h * (ka * kw) := by simp [mul_assoc]
      · change P.tc.rat (diagGL ν) * P.tc.rat weylGL * gS * (T.toList.map g).prod =
          (P.tc.aS (S.diagU ν) * P.tc.wS * gS) *
            (U.toList.map (thetaWhit_localArgument P ν true T g)).prod * (ka * kw)
        rw [P.tc.rat_diag ν, P.tc.rat_weyl, hAExt, hWExt, ← hGprod]
        have hLocal' :
            (U.toList.map (thetaWhit_localArgument P ν true T g)).prod = Aprod * Wprod * Gprod := by
          simpa [Wprod, wF] using hLocal
        rw [hLocal']
        have hKa_wS : ka * P.tc.wS = P.tc.wS * ka := P.tc.Kext_comm_S ka hkaK P.tc.wS P.tc.wS_mem
        have hKw_gS : kw * gS = gS * kw := P.tc.Kext_comm_S kw hkwK gS hgS
        have hKa_W : ka * Wprod = Wprod * ka := by
          exact list_mul_prod_commute ka U.toList wF (by
            intro v hv
            simpa [wF] using hkaComm v (Finset.mem_toList.mp hv) (wF v) (hwLoc v hv))
        have hKw_G : kw * Gprod = Gprod * kw := by
          apply list_mul_prod_commute kw U.toList gF
          intro v hv
          by_cases hvT : v ∈ T
          · simpa [gF, hvT] using hkwComm v (Finset.mem_toList.mp hv) (g v) (hg v hvT)
          · simp [gF, hvT]
        have hTail_gS : (ka * kw) * gS = gS * (ka * kw) := by
          calc
            (ka * kw) * gS = ka * (kw * gS) := by simp [mul_assoc]
            _ = ka * (gS * kw) := by rw [hKw_gS]
            _ = (ka * gS) * kw := by simp [mul_assoc]
            _ = (gS * ka) * kw := by rw [hKa_gS]
            _ = gS * (ka * kw) := by simp [mul_assoc]
        have hTail_G : (ka * kw) * Gprod = Gprod * (ka * kw) := by
          calc
            (ka * kw) * Gprod = ka * (kw * Gprod) := by simp [mul_assoc]
            _ = ka * (Gprod * kw) := by rw [hKw_G]
            _ = (ka * Gprod) * kw := by simp [mul_assoc]
            _ = (Gprod * ka) * kw := by rw [hKa_G]
            _ = Gprod * (ka * kw) := by simp [mul_assoc]
        have hA_wS : Aprod * P.tc.wS = P.tc.wS * Aprod := by
          have h := list_mul_prod_commute P.tc.wS U.toList aF (by
            intro v hv
            exact (P.tc.comm_S v (hU v (Finset.mem_toList.mp hv)) (aF v)
              (P.tc.a_mem v (toLoc v ν)) P.tc.wS P.tc.wS_mem).symm)
          exact h.symm
        have hW_gS : Wprod * gS = gS * Wprod := by
          have h := list_mul_prod_commute gS U.toList wF (by
            intro v hv
            exact (P.tc.comm_S v (hU v (Finset.mem_toList.mp hv)) (wF v) (hwLoc v hv) gS hgS).symm)
          exact h.symm
        have hAW_gS : (Aprod * Wprod) * gS = gS * (Aprod * Wprod) := by
          calc
            (Aprod * Wprod) * gS = Aprod * (Wprod * gS) := by simp [mul_assoc]
            _ = Aprod * (gS * Wprod) := by rw [hW_gS]
            _ = (Aprod * gS) * Wprod := by simp [mul_assoc]
            _ = (gS * Aprod) * Wprod := by rw [hA_gS]
            _ = gS * (Aprod * Wprod) := by simp [mul_assoc]
        calc
          P.tc.aS (S.diagU ν) *
              ((U.toList.map fun v => P.tc.a v (toLoc v ν)).prod * ka) *
              (P.tc.wS * ((U.toList.map P.tc.w).prod * kw)) * gS * Gprod =
              (P.tc.aS (S.diagU ν) * (Aprod * ka)) * P.tc.wS *
                ((Wprod * kw) * gS) * Gprod := by simp [Aprod, aF, Wprod, wF, mul_assoc]
          _ = (P.tc.aS (S.diagU ν) * (Aprod * ka)) * P.tc.wS *
              ((Wprod * kw) * gS) * Gprod := by rfl
          _ =
              P.tc.aS (S.diagU ν) * Aprod * ka * P.tc.wS * Wprod * kw * gS * Gprod := by
                simp [mul_assoc]
          _ = P.tc.aS (S.diagU ν) * Aprod * P.tc.wS * ka * Wprod * kw * gS * Gprod := by
                simpa [mul_assoc] using mul_swap_middle
                  (P.tc.aS (S.diagU ν) * Aprod) ka P.tc.wS
                  (Wprod * kw * gS * Gprod) hKa_wS
          _ = P.tc.aS (S.diagU ν) * Aprod * P.tc.wS * Wprod * ka * kw * gS * Gprod := by
                simpa [mul_assoc] using mul_swap_middle
                  (P.tc.aS (S.diagU ν) * Aprod * P.tc.wS) ka Wprod
                  (kw * gS * Gprod) hKa_W
          _ = P.tc.aS (S.diagU ν) * Aprod * P.tc.wS * Wprod * gS * (ka * kw) * Gprod := by
                simpa [mul_assoc] using mul_swap_middle
                  (P.tc.aS (S.diagU ν) * Aprod * P.tc.wS * Wprod) (ka * kw) gS Gprod hTail_gS
          _ = P.tc.aS (S.diagU ν) * Aprod * P.tc.wS * Wprod * gS * Gprod * (ka * kw) := by
                simpa [mul_assoc] using mul_swap_middle
                  (P.tc.aS (S.diagU ν) * Aprod * P.tc.wS * Wprod * gS) (ka * kw) Gprod 1 hTail_G
          _ = P.tc.aS (S.diagU ν) * P.tc.wS * Aprod * Wprod * gS * Gprod * (ka * kw) := by
                simpa [mul_assoc] using mul_swap_middle
                  (P.tc.aS (S.diagU ν)) Aprod P.tc.wS
                  (Wprod * gS * Gprod * (ka * kw)) hA_wS
          _ = P.tc.aS (S.diagU ν) * P.tc.wS * gS * Aprod * Wprod * Gprod * (ka * kw) := by
                simpa [mul_assoc] using mul_swap_middle
                  (P.tc.aS (S.diagU ν) * P.tc.wS) (Aprod * Wprod) gS
                  (Gprod * (ka * kw)) hAW_gS
          _ = (P.tc.aS (S.diagU ν) * P.tc.wS * gS) *
                (Aprod * Wprod * Gprod) * (ka * kw) := by simp [mul_assoc]
      · obtain ⟨xka, hxkaq, hxkaS, hxkaExt, hxkaC⟩ :=
          aExt_tail_lift (P := P) ν U hU hν ka hAExt
        obtain ⟨xkw, hxkwq, hxkwS, hxkwExt, hxkwC⟩ :=
          wExt_tail_lift (P := P) U hU kw hWExt
        have hxq : P.q (xka * xkw) = ka * kw := by
          rw [P.q.map_mul, hxkaq, hxkwq]
        have hxS : ∀ v, v ∈ S.Sf → P.compF v (xka * xkw) = 1 := by
          intro v hv
          rw [(P.compF v).map_mul, hxkaS v hv, hxkwS v hv]
          simp
        have hxExt : ∀ v (hv : v ∉ S.Sf),
            P.compF v (xka * xkw) ∈ (P.tame v hv).Kmax := by
          intro v hv
          rw [(P.compF v).map_mul]
          exact (P.tame v hv).Kmax.mul_mem (hxkaExt v hv) (hxkwExt v hv)
        have hxC : ∀ w, P.compC w (xka * xkw) = 1 := by
          intro w
          rw [(P.compC w).map_mul, hxkaC w, hxkwC w]
          simp
        exact scalarOf_right_of_components Fam hT (ka * kw) (xka * xkw)
          hxq hxS hxExt hxC

end ArtinPrimitiveRoots.A1.Theta
