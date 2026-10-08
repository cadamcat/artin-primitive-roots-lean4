import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.CoordinateEnvelope
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.ProbabilityGrouping
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.EdgePartition
import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.NormalizerGrowth

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical MeasureTheory
noncomputable section

/-- A uniform canonical-root grid estimate gives the absolute one-edge bad-source estimate. -/
theorem physical_bad_envelope_sum_upper {K : ℕ} (F : PDFix K) (S : PDScale)
    [Fintype (PState F S)] (hU : 0 < S.U) (hV : 0 < S.V) (hY : 0 < S.Y)
    (hL : 0 ≤ S.L) (R B G b E : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hG : 0 ≤ G) (hb : 0 ≤ b) (hE : 0 ≤ E)
    (hBand : ∀ i : Fin K, 0 < bandMass S.x (F.a i))
    (hBands : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a j)))
    (Z : Finset (ℤ × ℤ))
    (hZ : ∀ P Q : PState F S, 0 < physicalEnvelope F S R B P Q → edgeCoordinates P Q ∈ Z)
    (hGood : ∀ P : PState F S, (∫ r in (0 : ℝ)..1,
      if IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a P.labels r then (0 : ℝ) else 1) ≤ G)
    (hRoot : ∀ P Q : PState F S, 0 < physicalEnvelope F S R B P Q →
      ∀ T : Finset (PState F S × PState F S),
      (∀ e ∈ T, IsSlotTransition e.1.labels e.2.labels) →
      (∀ e ∈ T, physicalEdgeKey F S e = physicalEdgeKey F S (P, Q)) →
      (∀ e ∈ T, ¬ IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a e.1.labels (stateRoot e.1)) →
      (T.card : ℝ) ≤ S.U * S.V *
        ((6 / Real.pi ^ 2) * ∏ q ∈
          (∏ i : Fin K, ∏ j : Fin (slotCount S.x + 1), edgeUnionLabels P.labels Q.labels i j).primeFactors,
          ((q : ℝ) + 1)⁻¹) *
        (27 * volume.real (normalizedRootRegion ∩ {y | badEdgePredicate F S P.labels (edgeCoordinates P Q) y}) + b) + E) :
    let H := 32 * B * Real.rpow S.L (3 * F.A₀) / S.Y
    let σ := ∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ ^ (momentJ S.x + 2)
    physicalMeasure S.x K F.a * (∑ P : PState F S, ∑ Q : PState F S,
      if ¬ IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a P.labels (stateRoot P)
      then physicalEnvelope F S R B P Q else 0) ≤
      (S.U * S.V * (6 / Real.pi ^ 2)) *
        (27 * ((17 + H * (17 * (2 * R * S.Y + 1))) * (15 * G)) + b * (Z.card : ℝ) * (1 + H)) +
      E * σ * (Fintype.card (UnionLineChoice S.x F.a (slotCount S.x + 1)) : ℝ) * (Z.card : ℝ) * (1 + H) := by
  let H := 32 * B * Real.rpow S.L (3 * F.A₀) / S.Y
  let ν := ∏ i : Fin K, (bandMass S.x (F.a i))⁻¹
  let μ := physicalMeasure S.x K F.a
  let σ := ∏ i : Fin K, (bandMass S.x (F.a i))⁻¹ ^ (momentJ S.x + 2)
  have hPow := Real.rpow_nonneg hL (3 * F.A₀)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hν : 0 ≤ ν := Finset.prod_nonneg (fun i hi => inv_nonneg.mpr (hBand i).le)
  have hμ : 0 ≤ μ := by
    unfold μ physicalMeasure
    exact Finset.prod_nonneg (fun i hi => Real.rpow_nonneg (hBand i).le _)
  have hσ : 0 ≤ σ := Finset.prod_nonneg (fun i hi => pow_nonneg (inv_nonneg.mpr (hBand i).le) _)
  have hσeq : μ * ν = σ := physicalMeasure_fresh_eq_groupedNormalizer hBand
  have hEnv (P Q : PState F S) : 0 ≤ physicalEnvelope F S R B P Q := by
    unfold physicalEnvelope geometricEnvelope
    split_ifs <;> positivity
  have hTransition (P Q : PState F S) (hp : 0 < physicalEnvelope F S R B P Q) :
      IsSlotTransition P.labels Q.labels := by
    by_contra hn
    simp [physicalEnvelope, hn] at hp
  let T : Finset (PState F S × PState F S) := Finset.univ.filter fun e =>
    ¬ IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a e.1.labels (stateRoot e.1) ∧
      0 < physicalEnvelope F S R B e.1 e.2
  have hTpos (e : PState F S × PState F S) (he : e ∈ T) : 0 < physicalEnvelope F S R B e.1 e.2 :=
    (Finset.mem_filter.mp he).2.2
  have hTbad (e : PState F S × PState F S) (he : e ∈ T) :
      ¬ IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a e.1.labels (stateRoot e.1) := (Finset.mem_filter.mp he).2.1
  have hTtrans (e : PState F S × PState F S) (he : e ∈ T) := hTransition e.1 e.2 (hTpos e he)
  have hTotal : (∑ P : PState F S, ∑ Q : PState F S,
      if ¬ IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a P.labels (stateRoot P)
      then physicalEnvelope F S R B P Q else 0) =
      ∑ e ∈ T, physicalEnvelope F S R B e.1 e.2 := by
    rw [Finset.sum_filter]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro P hP
    apply Finset.sum_congr rfl
    intro Q hQ
    by_cases hbP : ¬ IsGoodRatio S.x S.Y (S.d₀ : ℝ) K F.a P.labels (stateRoot P)
    · by_cases hp : 0 < physicalEnvelope F S R B P Q
      · simp [hbP, hp]
      · have hz : physicalEnvelope F S R B P Q = 0 := le_antisymm (le_of_not_gt hp) (hEnv P Q)
        simp [hbP, hp, hz]
    · simp [hbP]
  rw [hTotal]
  by_cases hTempty : T = ∅
  · rw [hTempty, Finset.sum_empty, mul_zero]
    positivity
  obtain ⟨e₀, he₀⟩ := Finset.nonempty_iff_ne_empty.mpr hTempty
  let choices := T.image (fun e => physicalEdgeUnionChoice F S e.1 e.2)
  let repr (k : UnionLineChoice S.x F.a (slotCount S.x + 1)) : PState F S × PState F S :=
    if hk : k ∈ choices then (Finset.mem_image.mp hk).choose else e₀
  have hrepr (k : UnionLineChoice S.x F.a (slotCount S.x + 1)) (hk : k ∈ choices) :
      repr k ∈ T ∧ physicalEdgeUnionChoice F S (repr k).1 (repr k).2 = k := by
    simp only [repr, dif_pos hk]
    exact (Finset.mem_image.mp hk).choose_spec
  let w := unionLineWeight S.x F.a (N := slotCount S.x + 1)
  let c (k : UnionLineChoice S.x F.a (slotCount S.x + 1)) (z : ℤ × ℤ) :=
    coordinateEnvelope (sharedProduct (repr k).1.labels) (lastProduct (repr k).2.labels)
      (lastProduct (repr k).1.labels) S.Y R H z
  let m (k : UnionLineChoice S.x F.a (slotCount S.x + 1)) (z : ℤ × ℤ) :=
    volume.real (normalizedRootRegion ∩ {y | badEdgePredicate F S (repr k).1.labels z y})
  let M := (17 + H * (17 * (2 * R * S.Y + 1))) * (15 * G)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hw (k : UnionLineChoice S.x F.a (slotCount S.x + 1)) : 0 ≤ w k :=
    Finset.prod_nonneg (fun q hq => unionLineAtom_nonneg hBand q.1 (k q))
  have hmodel (k : UnionLineChoice S.x F.a (slotCount S.x + 1)) : ∑ z ∈ Z, m k z * c k z ≤ M := by
    apply (coordinateEnvelope_model_sum_le F S hU hV hY (repr k).1.labels Z
      (sharedProduct (repr k).1.labels) (lastProduct (repr k).2.labels) (lastProduct (repr k).1.labels)
      R H hR hH).trans
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hGood (repr k).1) (by norm_num))
      (by positivity)
  have hfiber (k : UnionLineChoice S.x F.a (slotCount S.x + 1)) (hk : k ∈ Finset.univ)
      (z : ℤ × ℤ) (hz : z ∈ Z) :
      μ * (∑ e ∈ T.filter (fun e => physicalEdgeKey F S e = (k, z)), physicalEnvelope F S R B e.1 e.2) ≤
        (S.U * S.V * (6 / Real.pi ^ 2)) * w k * (27 * m k z * c k z + b * c k z) + E * σ * c k z := by
    let Tz := T.filter fun e => physicalEdgeKey F S e = (k, z)
    have hc : 0 ≤ c k z := (coordinateEnvelope_nonneg_le _ _ _ _ _ _ hH z).1
    have hRHS : 0 ≤ (S.U * S.V * (6 / Real.pi ^ 2)) * w k * (27 * m k z * c k z + b * c k z) + E * σ * c k z := by
      have hm : 0 ≤ m k z := measureReal_nonneg
      have hwk := hw k
      positivity
    by_cases hEmpty : Tz = ∅
    · change μ * (∑ e ∈ Tz, _) ≤ _
      rw [hEmpty, Finset.sum_empty, mul_zero]
      exact hRHS
    obtain ⟨e, he⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
    obtain ⟨heT, hekey⟩ := Finset.mem_filter.mp he
    have hChoice : physicalEdgeUnionChoice F S e.1 e.2 = k := congrArg Prod.fst hekey
    have heCoords : edgeCoordinates e.1 e.2 = z := congrArg Prod.snd hekey
    have hkChoice : k ∈ choices := Finset.mem_image.mpr ⟨e, heT, hChoice⟩
    have hr := hrepr k hkChoice
    have hlabels := physicalEdgeUnionChoice_labels_eq F S e (repr k) (hTtrans e heT)
      (hTtrans _ hr.1) (hChoice.trans hr.2.symm)
    have hCount := hRoot e.1 e.2 (hTpos e heT) Tz
      (fun e' he' => hTtrans e' (Finset.mem_filter.mp he').1)
      (fun e' he' => (Finset.mem_filter.mp he').2.trans hekey.symm)
      (fun e' he' => hTbad e' (Finset.mem_filter.mp he').1)
    have hBound : (∑ e' ∈ Tz, physicalEnvelope F S R B e'.1 e'.2) ≤ (Tz.card : ℝ) * (ν * c k z) := by
      calc
        _ ≤ ∑ e' ∈ Tz, ν * c k z := by
          apply Finset.sum_le_sum
          intro e' he'
          have hdata := physicalEdgeKey_data F S e' e (hTtrans _ (Finset.mem_filter.mp he').1)
            (hTtrans e heT) ((Finset.mem_filter.mp he').2.trans hekey.symm)
          have hp := physicalEnvelope_le_coordinateEnvelope F S R B hBand hY hB hL e'.1 e'.2
          simpa only [hdata.1, hdata.2.1, hdata.2.2, hlabels.1, hlabels.2, heCoords] using hp
        _ = _ := by simp [nsmul_eq_mul]
    have hProb : σ * (∏ q ∈
        (∏ i : Fin K, ∏ j : Fin (slotCount S.x + 1), edgeUnionLabels e.1.labels e.2.labels i j).primeFactors,
        ((q : ℝ) + 1)⁻¹) = w k := by
      have hinj := edgeUnionLabels_address_injective e.1.labels e.2.labels
        ⟨fun i j => ⟨e.1.label_prime i j, e.1.label_in_band i j⟩, e.1.label_distinct⟩
        ⟨fun i j => ⟨e.2.label_prime i j, e.2.label_in_band i j⟩, e.2.label_distinct⟩ (hTtrans e heT) hBands
      have hh := unionLinePrimeProbability_factorization F.a (physicalEdgeUnionChoice F S e.1 e.2) hinj
      simpa only [physicalEdgeUnionChoice, slotCount, hChoice, σ, w, Nat.add_assoc, Nat.reduceAdd] using hh
    have hCount' : (Tz.card : ℝ) ≤ S.U * S.V *
        ((6 / Real.pi ^ 2) * ∏ q ∈
          (∏ i : Fin K, ∏ j : Fin (slotCount S.x + 1), edgeUnionLabels e.1.labels e.2.labels i j).primeFactors,
          ((q : ℝ) + 1)⁻¹) * (27 * m k z + b) + E := by
      simpa only [hlabels.1, heCoords] using hCount
    calc
      _ ≤ μ * ((Tz.card : ℝ) * (ν * c k z)) := mul_le_mul_of_nonneg_left hBound hμ
      _ = σ * (Tz.card : ℝ) * c k z := by rw [← hσeq]; ring
      _ ≤ σ * (S.U * S.V *
          ((6 / Real.pi ^ 2) * ∏ q ∈
            (∏ i : Fin K, ∏ j : Fin (slotCount S.x + 1), edgeUnionLabels e.1.labels e.2.labels i j).primeFactors,
            ((q : ℝ) + 1)⁻¹) * (27 * m k z + b) + E) * c k z :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCount' hσ) hc
      _ = _ := by
        have heq : σ * (S.U * S.V *
            ((6 / Real.pi ^ 2) * ∏ q ∈
              (∏ i : Fin K, ∏ j : Fin (slotCount S.x + 1), edgeUnionLabels e.1.labels e.2.labels i j).primeFactors,
              ((q : ℝ) + 1)⁻¹) * (27 * m k z + b) + E) * c k z =
            (S.U * S.V * (6 / Real.pi ^ 2)) *
              (σ * ∏ q ∈
                (∏ i : Fin K, ∏ j : Fin (slotCount S.x + 1), edgeUnionLabels e.1.labels e.2.labels i j).primeFactors,
                ((q : ℝ) + 1)⁻¹) * (27 * m k z * c k z + b * c k z) + E * σ * c k z := by ring
        rw [heq, hProb]
  have hkey (e : PState F S × PState F S) (he : e ∈ T) :
      physicalEdgeKey F S e ∈ (Finset.univ : Finset (UnionLineChoice S.x F.a (slotCount S.x + 1))) ×ˢ Z :=
    Finset.mem_product.mpr ⟨Finset.mem_univ _, hZ _ _ (hTpos e he)⟩
  have hp := probability_grouping_upper T Finset.univ Z (physicalEdgeKey F S) hkey
    (fun e => physicalEnvelope F S R B e.1 e.2) w c m μ (S.U * S.V * (6 / Real.pi ^ 2)) b E σ (1 + H) M
    (by positivity) hb hE hσ (by positivity) hM (fun k hk => hw k)
    (unionLineWeight_sum_le_one F.a _ hBand)
    (fun k hk z hz => coordinateEnvelope_nonneg_le _ _ _ _ _ _ hH z)
    (fun k hk => hmodel k) hfiber
  simpa only [Finset.card_univ] using hp

end
end ArtinPrimitiveRoots.TypeII.PD
