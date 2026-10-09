import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.Mass

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- Eta-supported fresh prime products have mass at most a fixed constant divided by Y. -/
theorem clean_product_mass_le {K : ℕ} (x : ℝ) (a : Fin K → ℝ) (q Y : ℝ)
    (hY : 0 < Y)
    (hV : ∀ i : Fin K, Real.log 2 / 2 ≤ bandMass x (a i))
    (hb : ∀ i : Fin K, ∀ p ∈ primeBand x (a i), (1/2 : ℝ) ≤ memoryBPrime x q p)
    (p : Fin K → ℕ) (hp : IsMarkedPrimeTuple x K a p)
    (hprod : Y ≤ (tupleProduct p : ℝ)) :
    0 ≤ (∏ i : Fin K, memoryNu x K a q i (p i)) ∧
      (∏ i : Fin K, memoryNu x K a q i (p i)) ≤ (4/Real.log 2)^K/Y := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hVp (i : Fin K) : 0 < bandMass x (a i) := by
    have h := hV i
    linarith
  have hpp (i : Fin K) : 0 < p i := (Finset.mem_filter.mp (hp i)).2.1.pos
  have hν (i : Fin K) : 0 ≤ memoryNu x K a q i (p i) ∧
      memoryNu x K a q i (p i) ≤ 2*(1/(bandMass x (a i)*(p i : ℝ))) :=
    pd4c_memoryNu_le_twice_mu q i (p i) (hpp i) (hVp i) (hb i (p i) (hp i))
  have hpoint (i : Fin K) : memoryNu x K a q i (p i) ≤ (4/Real.log 2)/(p i : ℝ) := by
    have hpr : 0 < (p i : ℝ) := by exact_mod_cast hpp i
    calc
      _ ≤ 2*(1/(bandMass x (a i)*(p i : ℝ))) := (hν i).2
      _ = (2/bandMass x (a i))/(p i : ℝ) := by field_simp [(hVp i).ne', hpr.ne']
      _ ≤ _ := div_le_div_of_nonneg_right
        ((div_le_div_iff₀ (hVp i) hlog).mpr (by linarith [hV i])) hpr.le
  refine ⟨Finset.prod_nonneg (fun i hi => (hν i).1), ?_⟩
  calc
    _ ≤ ∏ i : Fin K, (4/Real.log 2)/(p i : ℝ) :=
      Finset.prod_le_prod₀ (fun i hi => (hν i).1) (fun i hi => hpoint i)
    _ = (4/Real.log 2)^K/(tupleProduct p : ℝ) := by
      rw [Finset.prod_div_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        tupleProduct, Nat.cast_prod]
    _ ≤ _ := div_le_div_of_nonneg_left (pow_nonneg (by positivity) _) hY hprod

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
