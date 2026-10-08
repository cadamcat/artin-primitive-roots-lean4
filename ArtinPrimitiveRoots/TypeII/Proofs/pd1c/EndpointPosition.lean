import ArtinPrimitiveRoots.TypeII.PD.Determinant
import ArtinPrimitiveRoots.TypeII.Proofs.pd1c.BandGeometry

namespace ArtinPrimitiveRoots.TypeII.PD

open Classical ArtinPrimitiveRoots.TypeII Filter

set_option maxHeartbeats 1000000

lemma pd1c_prime_prod_squarefree {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    Squarefree (∏ i, p i) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes (hp i) (hp j)).mpr (hinj.ne hij))
  · intro i hi
    exact (hp i).squarefree

lemma pd1c_state_labels_injective {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (P : PhysicalState x K a H' Hm Hn)
    (hSep : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j))) :
    Function.Injective (fun z : Fin K × Fin (slotCount x) => P.labels z.1 z.2) := by
  rintro ⟨i, k⟩ ⟨j, l⟩ heq
  change P.labels i k = P.labels j l at heq
  by_cases hij : i = j
  · subst j
    have hkl : k = l := by
      by_contra hkl
      exact P.label_distinct i k l hkl heq
    subst l
    rfl
  · have hmem : P.labels i k ∈ primeBand x (a j) := by
      rw [heq]
      exact P.label_in_band j l
    exact (Finset.disjoint_left.mp (hSep i j hij) (P.label_in_band i k) hmem).elim

lemma pd1c_state_product_eq_pair_prod {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (P : PhysicalState x K a H' Hm Hn) :
    groupLabelProduct P = ∏ z : Fin K × Fin (slotCount x), P.labels z.1 z.2 := by
  symm
  rw [← Finset.univ_product_univ, Finset.prod_product]
  rfl

lemma pd1c_state_product_squarefree {x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (P : PhysicalState x K a H' Hm Hn)
    (hSep : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j))) :
    Squarefree (groupLabelProduct P) := by
  rw [pd1c_state_product_eq_pair_prod]
  exact pd1c_prime_prod_squarefree (fun z : Fin K × Fin (slotCount x) => P.labels z.1 z.2)
    (fun z : Fin K × Fin (slotCount x) => P.label_prime z.1 z.2) (pd1c_state_labels_injective P hSep)

lemma pd1c_endpoint_products_equal
    {δ C c₁ c₂ x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (hMin : family.xMin ≤ x)
    (hSep : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (hBelow : ∀ i : Fin K, ∀ p ∈ primeBand x (a i), (p : ℝ) < roughCutoff x)
    (P Q : PhysicalState x K a H' Hm Hn) (hfirst : P.first = Q.first)
    (hα : family.alpha x (P.first / groupLabelProduct P) ≠ 0) :
    groupLabelProduct P = groupLabelProduct Q := by
  let ι := Fin K × Fin (slotCount x)
  let p : ι → ℕ := fun z => P.labels z.1 z.2
  let q : ι → ℕ := fun z => Q.labels z.1 z.2
  have hPInj : Function.Injective p := pd1c_state_labels_injective P hSep
  have hQInj : Function.Injective q := pd1c_state_labels_injective Q hSep
  have hrough := (family.rough_support x hMin _ hα).2
  have hdiv := pd1c_groupLabelProduct_dvd_first P (pd1c_state_product_squarefree P hSep)
  have hfirstEq : groupLabelProduct P * (P.first / groupLabelProduct P) = P.first :=
    Nat.mul_div_cancel' hdiv
  have hsub : (Finset.univ.image q) ⊆ (Finset.univ.image p) := by
    intro r hr
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hr
    have hprime : (q z).Prime := Q.label_prime z.1 z.2
    have hqdiv : q z ∣ groupLabelProduct P * (P.first / groupLabelProduct P) := by
      rw [hfirstEq, hfirst]
      exact Q.label_divides z.1 z.2
    have hqprod : q z ∣ groupLabelProduct P := by
      rcases hprime.dvd_mul.mp hqdiv with h | h
      · exact h
      · have hlarge := hrough (q z) hprime h
        have hsmall := hBelow z.1 (q z) (Q.label_in_band z.1 z.2)
        linarith
    rw [pd1c_state_product_eq_pair_prod P] at hqprod
    obtain ⟨w, hw, hqw⟩ := (hprime.prime.dvd_finsetProd_iff _).mp hqprod
    have heq : q z = p w := by
      have hd := (Nat.dvd_prime (P.label_prime w.1 w.2)).mp hqw
      rcases hd with hd | hd
      · exact (hprime.ne_one hd).elim
      · exact hd
    exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, heq.symm⟩
  have hCardP : (Finset.univ.image p).card = Fintype.card ι := by
    rw [Finset.card_image_of_injective _ hPInj, Finset.card_univ]
  have hCardQ : (Finset.univ.image q).card = Fintype.card ι := by
    rw [Finset.card_image_of_injective _ hQInj, Finset.card_univ]
  have hImages : Finset.univ.image p = Finset.univ.image q := by
    apply (Finset.eq_of_subset_of_card_le hsub (by rw [hCardP, hCardQ])).symm
  have hprodP : (∏ z : ι, p z) = ∏ r ∈ Finset.univ.image p, r := by
    rw [Finset.prod_image (by intro i hi j hj heq; exact hPInj heq)]
  have hprodQ : (∏ z : ι, q z) = ∏ r ∈ Finset.univ.image q, r := by
    rw [Finset.prod_image (by intro i hi j hj heq; exact hQInj heq)]
  rw [pd1c_state_product_eq_pair_prod P, pd1c_state_product_eq_pair_prod Q]
  change (∏ z : ι, p z) = ∏ z : ι, q z
  rw [hprodP, hprodQ, hImages]

lemma pd1c_endpoint_position_constant
    {δ C c₁ c₂ x : ℝ} {K : ℕ} {a : Fin K → ℝ} {H' Hm Hn : ℝ}
    (family : CoefficientFamily δ C c₁ c₂) (hMin : family.xMin ≤ x) (beta : ℕ → ℂ)
    (hSep : ∀ i j : Fin K, i ≠ j → Disjoint (primeBand x (a i)) (primeBand x (a j)))
    (hBelow : ∀ i : Fin K, ∀ p ∈ primeBand x (a i), (p : ℝ) < roughCutoff x)
    (P Q : PhysicalState x K a H' Hm Hn) (hfirst : P.first = Q.first)
    (hsecond : P.second = Q.second) :
    endpointG x K a family beta P = endpointG x K a family beta Q := by
  have hPSq := pd1c_state_product_squarefree P hSep
  have hQSq := pd1c_state_product_squarefree Q hSep
  by_cases hPα : family.alpha x (P.first / groupLabelProduct P) = 0
  · by_cases hQα : family.alpha x (Q.first / groupLabelProduct Q) = 0
    · simp [endpointG, hPSq, hQSq, hPα, hQα]
    · have hprod := pd1c_endpoint_products_equal family hMin hSep hBelow Q P hfirst.symm hQα
      simp [endpointG, hPSq, hQSq, hfirst, hsecond, hprod]
  · have hprod := pd1c_endpoint_products_equal family hMin hSep hBelow P Q hfirst hPα
    simp [endpointG, hPSq, hQSq, hfirst, hsecond, hprod]



end ArtinPrimitiveRoots.TypeII.PD
