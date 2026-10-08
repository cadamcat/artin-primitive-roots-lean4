import ArtinPrimitiveRoots.TypeII.PD.Physical

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical

theorem groupLabelProduct_permute {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    {H' Hm Hn : ℝ} (P : PhysicalState x K a H' Hm Hn)
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) :
    groupLabelProduct (P.permute σ) = groupLabelProduct P := by
  unfold groupLabelProduct
  simp only [PhysicalState.permute]
  apply Finset.prod_congr rfl
  intro i hi
  exact Equiv.prod_comp (σ i) (fun j => P.labels i j)

theorem endpointF_permute {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    {H' Hm Hn : ℝ} (P : PhysicalState x K a H' Hm Hn)
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) :
    endpointF x K a family beta (P.permute σ) = endpointF x K a family beta P := by
  simp only [endpointF]
  rw [groupLabelProduct_permute]
  simp only [PhysicalState.permute]

theorem endpointG_permute {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    {H' Hm Hn : ℝ} (P : PhysicalState x K a H' Hm Hn)
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) :
    endpointG x K a family beta (P.permute σ) = endpointG x K a family beta P := by
  simp only [endpointG]
  rw [groupLabelProduct_permute]
  simp only [PhysicalState.permute]

theorem omissionProduct_permuteLists {x : ℝ} {K : ℕ} (p : PrimeLists x K)
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (omitted : Fin K → Fin (slotCount x)) :
    omissionProduct (permuteLists σ p) omitted =
      omissionProduct p (fun i => σ i (omitted i)) := by
  classical
  unfold omissionProduct permuteLists
  apply Finset.prod_congr rfl
  intro i hi
  calc
    (∏ j : Fin (slotCount x), if j ≠ omitted i then p i (σ i j) else 1) =
        ∏ j : Fin (slotCount x),
          if σ i j ≠ σ i (omitted i) then p i (σ i j) else 1 := by
            apply Finset.prod_congr rfl
            intro j hj
            have hcond : (j ≠ omitted i) ↔ σ i j ≠ σ i (omitted i) := by
              constructor
              · intro h heq
                exact h ((σ i).injective heq)
              · intro h heq
                exact h (congrArg (σ i) heq)
            simp only [hcond]
    _ = ∏ j : Fin (slotCount x), if j ≠ σ i (omitted i) then p i j else 1 :=
      Equiv.prod_comp (σ i) (fun j => if j ≠ σ i (omitted i) then p i j else 1)

@[simp] theorem goodTestOne_permuteLists {x Y d₀ : ℝ} {K : ℕ}
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (p : PrimeLists x K) (r : ℝ) :
    goodTestOne x Y d₀ (permuteLists σ p) r ↔ goodTestOne x Y d₀ p r := by
  constructor
  · intro h omitted hd₀ hupper l hl₁ hlY
    let omitted' : Fin K → Fin (slotCount x) := fun i => (σ i).symm (omitted i)
    have hprod := omissionProduct_permuteLists p σ omitted'
    have hprod' : omissionProduct (permuteLists σ p) omitted' = omissionProduct p omitted := by
      simpa [omitted'] using hprod
    have hlowQ : d₀ ≤ (omissionProduct (permuteLists σ p) omitted' : ℝ) := by
      simpa [hprod'] using hd₀
    have hupperQ : (omissionProduct (permuteLists σ p) omitted' : ℝ) < 2 * d₀ := by
      simpa [hprod'] using hupper
    have h := h omitted' hlowQ hupperQ l hl₁ hlY
    simpa [hprod'] using h
  · intro h omitted hd₀ hupper l hl₁ hlY
    let omitted' : Fin K → Fin (slotCount x) := fun i => σ i (omitted i)
    have hprod := omissionProduct_permuteLists p σ omitted
    have hprod' : omissionProduct (permuteLists σ p) omitted = omissionProduct p omitted' := by
      simpa [omitted'] using hprod
    have hlow' : d₀ ≤ (omissionProduct p omitted' : ℝ) := by simpa [hprod'] using hd₀
    have hupper' : (omissionProduct p omitted' : ℝ) < 2 * d₀ := by simpa [hprod'] using hupper
    have h := h omitted' hlow' hupper' l hl₁ hlY
    simpa [hprod'] using h

@[simp] theorem goodnessTrialValue_permuteLists {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (p : PrimeLists x K) (d₀ : ℝ)
    (I : Finset (Fin K)) (iStar : Fin K) (fresh : Fin K → ℕ) (n : ℕ) :
    IsGoodnessTrialValue a (permuteLists σ p) d₀ I iStar fresh n ↔
      IsGoodnessTrialValue a p d₀ I iStar fresh n := by
  unfold IsGoodnessTrialValue
  constructor
  · rintro ⟨omitted, z, heq, hlo, hhi, hz⟩
    let omitted' : Fin K → Fin (slotCount x) := fun i => σ i (omitted i)
    have hprod := omissionProduct_permuteLists p σ omitted
    have hprod' : omissionProduct (permuteLists σ p) omitted = omissionProduct p omitted' := by
      simpa [omitted'] using hprod
    have hlo' : d₀ ≤ (omissionProduct p omitted' : ℝ) := by simpa [hprod'] using hlo
    have hhi' : (omissionProduct p omitted' : ℝ) < 2 * d₀ := by simpa [hprod'] using hhi
    refine ⟨omitted', z, ?_, hlo', hhi', hz⟩
    simpa [hprod'] using heq
  · rintro ⟨omitted, z, heq, hlo, hhi, hz⟩
    let omitted' : Fin K → Fin (slotCount x) := fun i => (σ i).symm (omitted i)
    have hp := omissionProduct_permuteLists p σ omitted'
    have hprod' : omissionProduct (permuteLists σ p) omitted' = omissionProduct p omitted := by
      simpa [omitted'] using hp
    have hlo' : d₀ ≤ (omissionProduct (permuteLists σ p) omitted' : ℝ) := by
      simpa [hprod'] using hlo
    have hhi' : (omissionProduct (permuteLists σ p) omitted' : ℝ) < 2 * d₀ := by
      simpa [hprod'] using hhi
    refine ⟨omitted', z, ?_, hlo', hhi', hz⟩
    simpa [hprod'] using heq

@[simp] theorem goodTestTwo_permuteLists {x d₀ : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (p : PrimeLists x K) (r : ℝ) :
    goodTestTwo x d₀ K a (permuteLists σ p) r ↔ goodTestTwo x d₀ K a p r := by
  simp [goodTestTwo]

@[simp] theorem goodRatio_permuteLists {x Y d₀ : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (p : PrimeLists x K) (r : ℝ) :
    IsGoodRatio x Y d₀ K a (permuteLists σ p) r ↔ IsGoodRatio x Y d₀ K a p r := by
  unfold IsGoodRatio
  exact and_congr (goodTestOne_permuteLists σ p r)
    (goodTestTwo_permuteLists σ p r)

theorem stateRoot_permute {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    {H' Hm Hn : ℝ} (P : PhysicalState x K a H' Hm Hn)
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) :
    stateRoot (P.permute σ) = stateRoot P := by
  simp [stateRoot, PhysicalState.permute]

theorem isGoodRatio_statePermute {x Y d₀ : ℝ} {K : ℕ} {a : Fin K → ℝ}
    {H' Hm Hn : ℝ} (P : PhysicalState x K a H' Hm Hn)
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) :
    IsGoodRatio x Y d₀ K a (P.permute σ).labels (stateRoot (P.permute σ)) ↔
      IsGoodRatio x Y d₀ K a P.labels (stateRoot P) := by
  rw [stateRoot_permute]
  exact goodRatio_permuteLists σ P.labels (stateRoot P)

theorem physSym_eq_self_of_permuteInvariant {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : PState F S → ℂ) (P : PState F S)
    (hperm : ∀ Q σ, f (Q.permute σ) = f Q) : physSym F S f P = f P := by
  classical
  let G := Fin K → Equiv.Perm (Fin (slotCount S.x))
  haveI : Nonempty G := ⟨fun _ => Equiv.refl (Fin (slotCount S.x))⟩
  have hcardPos : 0 < permCount S.x K := by
    unfold permCount
    exact Fintype.card_pos_iff.mpr inferInstance
  have hcardNe : (permCount S.x K : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcardPos)
  have hsum :
      (∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)), f (P.permute σ)) =
        (permCount S.x K : ℂ) * f P := by
    calc
      _ = ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)), f P := by
        apply Finset.sum_congr rfl
        intro σ hσ
        exact hperm P σ
      _ = _ := by simp [permCount]
  unfold physSym
  rw [hsum]
  field_simp [hcardNe]

theorem physSym_endpointF {K : ℕ} (F : PDFix K) (S : PDScale)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    (P : PState F S) :
    physSym F S (endpointFVector S.x K F.a S.H S.Hm S.Hn family beta) P =
      endpointF S.x K F.a family beta P := by
  apply physSym_eq_self_of_permuteInvariant F S _ P
  intro Q σ
  simpa [endpointFVector] using endpointF_permute family beta Q σ

theorem physSym_endpointG {K : ℕ} (F : PDFix K) (S : PDScale)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    (P : PState F S) :
    physSym F S (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta) P =
      endpointG S.x K F.a family beta P := by
  apply physSym_eq_self_of_permuteInvariant F S _ P
  intro Q σ
  simpa [endpointGVector] using endpointG_permute family beta Q σ

theorem physSym_goodEndpointG {K : ℕ} (F : PDFix K) (S : PDScale)
    {δ C c₁ c₂ : ℝ} (family : CoefficientFamily δ C c₁ c₂) (beta : ℕ → ℂ)
    (P : PState F S) :
    physSym F S (physGood F S
      (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta)) P =
        physGood F S (endpointGVector S.x K F.a S.H S.Hm S.Hn family beta) P := by
  apply physSym_eq_self_of_permuteInvariant F S _ P
  intro Q σ
  unfold physGood endpointGVector
  rw [isGoodRatio_statePermute, endpointG_permute]

def statePermuteEquiv {K : ℕ} (F : PDFix K) (S : PDScale)
    (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) : PState F S ≃ PState F S where
  toFun := fun P => P.permute σ
  invFun := fun P => P.permute (fun i => (σ i).symm)
  left_inv := by
    intro P
    cases P
    simp [PhysicalState.permute]
  right_inv := by
    intro P
    cases P
    simp [PhysicalState.permute]

theorem sum_mul_physSym_eq_of_permuteInvariant {K : ℕ} (F : PDFix K) (S : PDScale)
    [Fintype (PState F S)] (w f : PState F S → ℂ)
    (hw : ∀ P σ, w (P.permute σ) = w P) :
    (∑ P, w P * physSym F S f P) = ∑ P, w P * f P := by
  classical
  let G := Fin K → Equiv.Perm (Fin (slotCount S.x))
  haveI : Nonempty G := ⟨fun _ => Equiv.refl (Fin (slotCount S.x))⟩
  have hcardPos : 0 < permCount S.x K := by
    unfold permCount
    exact Fintype.card_pos_iff.mpr inferInstance
  have hcardNe : (permCount S.x K : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hcardPos)
  have hpermSum (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) :
      (∑ P : PState F S, w P * f (PhysicalState.permute σ P)) =
        ∑ P : PState F S, w P * f P := by
    let e := statePermuteEquiv F S σ
    calc
      _ = ∑ P : PState F S,
            w (PhysicalState.permute σ P) * f (PhysicalState.permute σ P) := by
        apply Finset.sum_congr rfl
        intro P hP
        rw [← hw]
      _ = ∑ P : PState F S, (fun Q => w Q * f Q) (e P) := rfl
      _ = ∑ P : PState F S, w P * f P := Equiv.sum_comp e (fun Q => w Q * f Q)
  unfold physSym
  calc
    (∑ P, w P * ((permCount S.x K : ℂ)⁻¹ *
      ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)), f (P.permute σ))) =
        ∑ P, ((permCount S.x K : ℂ)⁻¹ *
          ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)), w P * f (P.permute σ)) := by
      apply Finset.sum_congr rfl
      intro P hP
      calc
        w P * ((permCount S.x K : ℂ)⁻¹ *
            ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)), f (P.permute σ)) =
            (permCount S.x K : ℂ)⁻¹ *
              (w P * ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)), f (P.permute σ)) := by ring
        _ = (permCount S.x K : ℂ)⁻¹ *
              ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)), w P * f (P.permute σ) := by
              rw [Finset.mul_sum]
    _ = (permCount S.x K : ℂ)⁻¹ *
          ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            ∑ P, w P * f (P.permute σ) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ = (permCount S.x K : ℂ)⁻¹ *
          ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)), ∑ P, w P * f P := by
      congr 1
      apply Finset.sum_congr rfl
      intro σ hσ
      exact hpermSum σ
    _ = ∑ P, w P * f P := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, permCount]
      field_simp [hcardNe]

end ArtinPrimitiveRoots.TypeII.PD
