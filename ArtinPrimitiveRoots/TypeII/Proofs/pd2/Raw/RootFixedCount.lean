import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootQuantitativeDiscrepancy
import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootEulerAverage

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

noncomputable def pd2a_fixedRootPredicate (u S : ℕ)
    (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) (l r : ℝ) (v : ℕ) : Prop :=
  Nat.Coprime u v ∧ ∃ c d : ℤ, (u : ℤ) * d - (v : ℤ) * c = 1 ∧
    0 ≤ c ∧ c < u ∧ l ≤ (c : ℝ) / u ∧ (c : ℝ) / u ≤ r ∧
      g₀ 0 0 = (u : ZMod S) ∧ g₀ 0 1 = (c : ZMod S) ∧
        g₀ 1 0 = (v : ZMod S) ∧ g₀ 1 1 = (d : ZMod S)

noncomputable def pd2a_fixedRootCount (u : ℕ) (V : ℝ) (S : ℕ)
    (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) (l₂ r₂ l₃ r₃ : ℝ) : ℝ :=
  ((pd2a_natClosedInterval (l₂ * V) (r₂ * V)).filter (pd2a_fixedRootPredicate u S g₀ l₃ r₃)).card

lemma pd2a_natCast_representative (m S n : ℕ) [NeZero m] (hdiv : S ∣ m) :
    (((n : ZMod m).val : ℕ) : ZMod S) = (n : ZMod S) := by
  rw [← pd2a_zmod_divisor_cast_value m S hdiv]
  exact map_natCast _ _

lemma pd2a_rootGraph_natural_membership (u S c v : ℕ) [NeZero (u * S)]
    (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) :
    ((c : ZMod (u * S)), (v : ZMod (u * S))) ∈ pd2a_rootGraph u S g₀ ↔
      (c : ZMod S) = g₀ 0 1 ∧ (v : ZMod S) = g₀ 1 0 ∧
      (c : ZMod (u * S)) * (v : ZMod (u * S)) = (u : ZMod (u * S)) * ((g₀ 1 1).val : ZMod (u * S)) - 1 := by
  simp only [pd2a_rootGraph, Finset.mem_filter, Finset.mem_univ, true_and,
    pd2a_natCast_representative (u * S) S c (dvd_mul_left S u),
    pd2a_natCast_representative (u * S) S v (dvd_mul_left S u)]

lemma pd2a_rootGraph_c_unique (u S c c' v : ℕ) (hu : 0 < u) [NeZero (u * S)]
    (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) (hc : c < u) (hc' : c' < u)
    (hG : ((c : ZMod (u * S)), (v : ZMod (u * S))) ∈ pd2a_rootGraph u S g₀)
    (hG' : ((c' : ZMod (u * S)), (v : ZMod (u * S))) ∈ pd2a_rootGraph u S g₀) : c = c' := by
  have hcong := ((pd2a_rootGraph_natural_membership u S c v g₀).mp hG).2.2
  have hcong' := ((pd2a_rootGraph_natural_membership u S c' v g₀).mp hG').2.2
  have hZ : (((c : ℤ) * (v : ℤ) : ℤ) : ZMod (u * S)) =
      (((u : ℤ) * ((g₀ 1 1).val : ℤ) - 1 : ℤ) : ZMod (u * S)) := by
    simpa only [Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.cast_one] using hcong
  have hZ' : (((c' : ℤ) * (v : ℤ) : ℤ) : ZMod (u * S)) =
      (((u : ℤ) * ((g₀ 1 1).val : ℤ) - 1 : ℤ) : ZMod (u * S)) := by
    simpa only [Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.cast_one] using hcong'
  obtain ⟨d, hdet, hd⟩ := (pd2a_completion_residue_iff u v S hu c (g₀ 1 1).val).mpr hZ
  obtain ⟨d', hdet', hd'⟩ := (pd2a_completion_residue_iff u v S hu c' (g₀ 1 1).val).mpr hZ'
  have hcop := pd2a_det_one_coprime u v c d hdet
  have hEq := (pd2a_root_completion_unique u v hu hcop c d c' d' hdet hdet'
    (by positivity) (by exact_mod_cast hc) (by positivity) (by exact_mod_cast hc')).1
  exact_mod_cast hEq

lemma pd2a_fixedPredicate_graph_indices (u S v : ℕ) (hu : 0 < u) (hS : 0 < S) [NeZero (u * S)]
    (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) (hu₀ : (u : ZMod S) = g₀ 0 0)
    (l r : ℝ) (hl : 0 ≤ l) (hlr : l ≤ r) (hr : r ≤ 1) :
    pd2a_fixedRootPredicate u S g₀ l r v ↔
      ∃ i ∈ Finset.range (pd2a_rootCLength u l r),
        (((pd2a_rootCStart u l + i : ℕ) : ZMod (u * S)), (v : ZMod (u * S))) ∈ pd2a_rootGraph u S g₀ := by
  rw [pd2a_fixedRootPredicate, pd2a_root_graph_natural_predicate u v S hu hS g₀ l r]
  constructor
  · rintro ⟨c, hcu, hcl, hcr, hgu, hgc, hgv, hcong⟩
    obtain ⟨i, hi, rfl⟩ := (pd2a_root_c_indices u c hu l r hl hlr hr).mp ⟨hcu, hcl, hcr⟩
    exact ⟨i, hi, (pd2a_rootGraph_natural_membership _ _ _ _ _).mpr ⟨hgc.symm, hgv.symm, hcong⟩⟩
  · rintro ⟨i, hi, hG⟩
    obtain ⟨hcu, hcl, hcr⟩ := (pd2a_root_c_indices u (pd2a_rootCStart u l + i) hu l r hl hlr hr).mpr ⟨i, hi, rfl⟩
    obtain ⟨hgc, hgv, hcong⟩ := (pd2a_rootGraph_natural_membership _ _ _ _ _).mp hG
    exact ⟨_, hcu, hcl, hcr, hu₀.symm, hgc.symm, hgv.symm, hcong⟩

lemma pd2a_fixedRootCount_density (u : ℕ) (V : ℝ) (S : ℕ) (hu : 0 < u) (hS : 0 < S)
    [NeZero (u * S)] (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S)) (hu₀ : (u : ZMod S) = g₀ 0 0)
    (l₂ r₂ l₃ r₃ : ℝ) (hV : 0 < V) (hl₂ : 0 ≤ l₂) (hlr₂ : l₂ ≤ r₂)
    (hl₃ : 0 ≤ l₃) (hlr₃ : l₃ ≤ r₃) (hr₃ : r₃ ≤ 1) :
    (pd2a_fixedRootCount u V S g₀ l₂ r₂ l₃ r₃ : ℂ) =
      ∑ z ∈ pd2a_rootGraph u S g₀,
        pd2a_rootIntervalDensity (u * S) (pd2a_rootCStart u l₃) (pd2a_rootCLength u l₃ r₃) z.1 *
          pd2a_rootIntervalDensity (u * S) (pd2a_intervalStart (l₂ * V))
            (pd2a_intervalLength (l₂ * V) (r₂ * V)) z.2 := by
  let ac := pd2a_rootCStart u l₃
  let Nc := pd2a_rootCLength u l₃ r₃
  let av := pd2a_intervalStart (l₂ * V)
  let Nv := pd2a_intervalLength (l₂ * V) (r₂ * V)
  let G := pd2a_rootGraph u S g₀
  let J := ((Finset.range Nc).product (Finset.range Nv)).filter (fun ij =>
    (((ac + ij.1 : ℕ) : ZMod (u * S)), ((av + ij.2 : ℕ) : ZMod (u * S))) ∈ G)
  let Vs := (pd2a_natClosedInterval (l₂ * V) (r₂ * V)).filter (pd2a_fixedRootPredicate u S g₀ l₃ r₃)
  have hA : 0 ≤ l₂ * V := mul_nonneg hl₂ hV.le
  have hAB : l₂ * V ≤ r₂ * V := mul_le_mul_of_nonneg_right hlr₂ hV.le
  have hB : 0 ≤ r₂ * V := hA.trans hAB
  have hData : ∀ ij ∈ J, ij.1 ∈ Finset.range Nc ∧ ij.2 ∈ Finset.range Nv ∧
      (((ac + ij.1 : ℕ) : ZMod (u * S)), ((av + ij.2 : ℕ) : ZMod (u * S))) ∈ G := by
    intro ij hij
    have h := Finset.mem_filter.mp hij
    exact ⟨(Finset.mem_product.mp h.1).1, (Finset.mem_product.mp h.1).2, h.2⟩
  let f : J → Vs := fun ij => ⟨av + ij.1.2, by
    obtain ⟨hi, hj, hG⟩ := hData ij.1 ij.2
    have hv := pd2a_interval_indices (l₂ * V) (r₂ * V) hA hAB ij.1.2 hj
    have hP := (pd2a_fixedPredicate_graph_indices u S (av + ij.1.2) hu hS g₀ hu₀
      l₃ r₃ hl₃ hlr₃ hr₃).mpr ⟨ij.1.1, hi, hG⟩
    exact Finset.mem_filter.mpr ⟨(pd2a_natClosedInterval_mem _ _ hB _).mpr hv, hP⟩⟩
  have hf : Function.Injective f := by
    intro ij kl hEq
    have hv : av + ij.1.2 = av + kl.1.2 := congrArg Subtype.val hEq
    have hjEq : ij.1.2 = kl.1.2 := Nat.add_left_cancel hv
    obtain ⟨hi, hj, hG⟩ := hData ij.1 ij.2
    obtain ⟨hki, hkj, hkG⟩ := hData kl.1 kl.2
    have hc : ac + ij.1.1 < u := ((pd2a_root_c_indices u (ac + ij.1.1) hu l₃ r₃ hl₃ hlr₃ hr₃).mpr ⟨ij.1.1, hi, rfl⟩).1
    have hkc : ac + kl.1.1 < u := ((pd2a_root_c_indices u (ac + kl.1.1) hu l₃ r₃ hl₃ hlr₃ hr₃).mpr ⟨kl.1.1, hki, rfl⟩).1
    have hkG' : (((ac + kl.1.1 : ℕ) : ZMod (u * S)), ((av + ij.1.2 : ℕ) : ZMod (u * S))) ∈ G := by rw [hjEq]; exact hkG
    have hcEq := pd2a_rootGraph_c_unique u S (ac + ij.1.1) (ac + kl.1.1) (av + ij.1.2) hu g₀ hc hkc hG hkG'
    exact Subtype.ext (Prod.ext (Nat.add_left_cancel hcEq) hjEq)
  have hsurj : Function.Surjective f := by
    intro v
    have hv := Finset.mem_filter.mp v.2
    obtain ⟨hLo, hHi⟩ := (pd2a_natClosedInterval_mem _ _ hB v.1).mp hv.1
    obtain ⟨j, hj, hvEq⟩ := pd2a_interval_index_exists (l₂ * V) (r₂ * V) hA hAB v.1 hLo hHi
    obtain ⟨i, hi, hG⟩ := (pd2a_fixedPredicate_graph_indices u S v.1 hu hS g₀ hu₀
      l₃ r₃ hl₃ hlr₃ hr₃).mp hv.2
    have hG' : (((ac + i : ℕ) : ZMod (u * S)), ((av + j : ℕ) : ZMod (u * S))) ∈ G := by simpa only [hvEq] using hG
    have hij : (i, j) ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hj⟩, hG'⟩
    refine ⟨⟨(i, j), hij⟩, ?_⟩
    apply Subtype.ext
    exact hvEq.symm
  have hCard : J.card = Vs.card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr (Equiv.ofBijective f ⟨hf, hsurj⟩)
  have hDensity := pd2a_density_count_identity (u * S) ac Nc av Nv G
  rw [hDensity]
  have hReal : pd2a_fixedRootCount u V S g₀ l₂ r₂ l₃ r₃ = (Vs.card : ℝ) := rfl
  rw [hReal, hCard]
  norm_cast

end ArtinPrimitiveRoots.TypeII.PD
