import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.UnionLabels
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.EdgeCoordinates
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.KernelEnvelope

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open ArtinPrimitiveRoots.TypeII Classical

noncomputable section

def physicalEdgeUnionChoice {K : ℕ} (F : PDFix K) (S : PDScale) (P Q : PState F S) :
    UnionLineChoice S.x F.a (slotCount S.x + 1) :=
  fun ij => ⟨edgeUnionLabels P.labels Q.labels ij.1 ij.2,
    (edgeUnionLabels_in_bands P.labels Q.labels
      ⟨fun i j => ⟨P.label_prime i j, P.label_in_band i j⟩, P.label_distinct⟩
      ⟨fun i j => ⟨Q.label_prime i j, Q.label_in_band i j⟩, Q.label_distinct⟩ ij.1 ij.2).2⟩

def physicalEdgeKey {K : ℕ} (F : PDFix K) (S : PDScale) (e : PState F S × PState F S) :
    UnionLineChoice S.x F.a (slotCount S.x + 1) × (ℤ × ℤ) :=
  (physicalEdgeUnionChoice F S e.1 e.2, edgeCoordinates e.1 e.2)

/-- Each label/vector group is counted injectively by the source's primitive position. -/
theorem physicalEdgeKey_root_injective {K : ℕ} (F : PDFix K) (S : PDScale)
    (e e' : PState F S × PState F S)
    (ht : IsSlotTransition e.1.labels e.2.labels) (ht' : IsSlotTransition e'.1.labels e'.2.labels)
    (hkey : physicalEdgeKey F S e = physicalEdgeKey F S e')
    (hroot : (e.1.first, e.1.second) = (e'.1.first, e'.1.second)) : e = e' := by
  have hChoice := congrArg Prod.fst hkey
  have hCoords := congrArg Prod.snd hkey
  have hLabels : edgeUnionLabels e.1.labels e.2.labels = edgeUnionLabels e'.1.labels e'.2.labels := by
    funext i j
    have h := congrArg (fun t => (t (i, j)).val) hChoice
    exact h
  obtain ⟨hPLabels, hQLabels⟩ := edgeUnionLabels_injective_on_transitions _ _ _ _ ht ht' hLabels
  have hFirst := congrArg Prod.fst hroot
  have hSecond := congrArg Prod.snd hroot
  have hP : e.1 = e'.1 := physicalState_eq_of_coordinates e.1 e'.1 hFirst hSecond hPLabels
  have hQ : e.2 = e'.2 := physicalTarget_eq_of_edgeCoordinates e.1 e.2 e'.2
    (by simpa only [physicalEdgeKey, hP] using hCoords) hQLabels
  exact Prod.ext hP hQ

/-- The physical envelope is constant on each active union-label/vector group. -/
theorem physicalEdgeKey_envelope_eq {K : ℕ} (F : PDFix K) (S : PDScale) (R B : ℝ)
    (e e' : PState F S × PState F S)
    (ht : IsSlotTransition e.1.labels e.2.labels) (ht' : IsSlotTransition e'.1.labels e'.2.labels)
    (hkey : physicalEdgeKey F S e = physicalEdgeKey F S e') :
    physicalEnvelope F S R B e.1 e.2 = physicalEnvelope F S R B e'.1 e'.2 := by
  have hChoice := congrArg Prod.fst hkey
  have hCoords := congrArg Prod.snd hkey
  have hLabels : edgeUnionLabels e.1.labels e.2.labels = edgeUnionLabels e'.1.labels e'.2.labels := by
    funext i j
    exact congrArg (fun t => (t (i, j)).val) hChoice
  obtain ⟨hPLabels, hQLabels⟩ := edgeUnionLabels_injective_on_transitions _ _ _ _ ht ht' hLabels
  have hDt : det2 e.1.pos e.2.pos = det2 e'.1.pos e'.2.pos := by
    rw [← edgeCoordinates_second_eq_det, ← edgeCoordinates_second_eq_det]
    exact congrArg Prod.snd hCoords
  unfold physicalEnvelope
  rw [hPLabels, hQLabels, hDt]


/-- A transition fiber and its source-root image have identical cardinality. -/
theorem physicalEdgeFiber_card_eq_roots {K : ℕ} (F : PDFix K) (S : PDScale)
    (E : Finset (PState F S × PState F S))
    (htransition : ∀ e ∈ E, IsSlotTransition e.1.labels e.2.labels)
    (key : UnionLineChoice S.x F.a (slotCount S.x + 1) × (ℤ × ℤ)) :
    (E.filter fun e => physicalEdgeKey F S e = key).card =
      ((E.filter fun e => physicalEdgeKey F S e = key).image (fun e => (e.1.first, e.1.second))).card := by
  symm
  apply Finset.card_image_of_injOn
  intro e he e' he' hroot
  obtain ⟨heE, heKey⟩ := Finset.mem_filter.mp he
  obtain ⟨heE', heKey'⟩ := Finset.mem_filter.mp he'
  exact physicalEdgeKey_root_injective F S e e' (htransition e heE) (htransition e' heE')
    (heKey.trans heKey'.symm) hroot

theorem physicalEdgeKey_data {K : ℕ} (F : PDFix K) (S : PDScale)
    (e e' : PState F S × PState F S)
    (ht : IsSlotTransition e.1.labels e.2.labels) (ht' : IsSlotTransition e'.1.labels e'.2.labels)
    (hkey : physicalEdgeKey F S e = physicalEdgeKey F S e') :
    e.1.labels = e'.1.labels ∧ e.2.labels = e'.2.labels ∧ edgeCoordinates e.1 e.2 = edgeCoordinates e'.1 e'.2 := by
  have hChoice := congrArg Prod.fst hkey
  have hCoords := congrArg Prod.snd hkey
  have hLabels : edgeUnionLabels e.1.labels e.2.labels = edgeUnionLabels e'.1.labels e'.2.labels := by
    funext i j
    exact congrArg (fun t => (t (i, j)).val) hChoice
  obtain ⟨hp, hq⟩ := edgeUnionLabels_injective_on_transitions _ _ _ _ ht ht' hLabels
  exact ⟨hp, hq, hCoords⟩



/-- The union choice alone determines both physical endpoint label lists. -/
theorem physicalEdgeUnionChoice_labels_eq {K : ℕ} (F : PDFix K) (S : PDScale)
    (e e' : PState F S × PState F S)
    (ht : IsSlotTransition e.1.labels e.2.labels) (ht' : IsSlotTransition e'.1.labels e'.2.labels)
    (heq : physicalEdgeUnionChoice F S e.1 e.2 = physicalEdgeUnionChoice F S e'.1 e'.2) :
    e.1.labels = e'.1.labels ∧ e.2.labels = e'.2.labels := by
  apply edgeUnionLabels_injective_on_transitions _ _ _ _ ht ht'
  funext i j
  exact congrArg (fun t => (t (i, j)).val) heq

end
end ArtinPrimitiveRoots.TypeII.PD
