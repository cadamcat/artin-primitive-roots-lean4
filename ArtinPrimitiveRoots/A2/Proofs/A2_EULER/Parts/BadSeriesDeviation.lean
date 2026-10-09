import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_euler_sol
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
  (η : HeckeChar F) (U : FrequencyData S D η)

theorem bad_series_deviation (u : U.U) (v : FinPlace F) (hv : v ∉ S.Sf) (p : Triple)
    (hp : eulerNeighborhood p) (hQ : (2 : ℝ) ^ (2000 : ℕ) < qI v.asIdeal)
    (hs : Summable (fun i : Fin 2 × ℕ × ℕ × ℕ =>
      ‖localEulerTerm R η U u v hv (p 0) (p 1) (p 2) i‖))
    (hVtail : ∀ m, localEulerTerm R η U u v hv (p 0) (p 1) (p 2) (0, 0, 0, m) =
      localV v (p 2) ^ m)
    (hsharp : ∀ i : Fin 2 × ℕ × ℕ × ℕ, 0 < i.1.1 + 3 * i.2.1 → i.2.2.1 ≤ 1 →
      ‖localEulerTerm R η U u v hv (p 0) (p 1) (p 2) i‖ ≤
        qI v.asIdeal ^ ((i.1.1 : ℝ) * (1 / 2 - (p 0).re) +
          (i.2.1 : ℝ) * (2 - 3 * (p 0).re) +
          (i.2.2.1 : ℝ) * (1 / 2 - (p 1).re) - 6 * (i.2.2.2 : ℝ) * (p 2).re))
    (hbase : localEulerTerm R η U u v hv (p 0) (p 1) (p 2) (0, 0, 0, 0) = 1)
    (ht0 : ∀ k m, k ≠ 0 → localEulerTerm R η U u v hv (p 0) (p 1) (p 2) (0, 0, k, m) = 0)
    (ht1 : localEulerTerm R η U u v hv (p 0) (p 1) (p 2) (1, 0, 0, 0) = 0)
    (hk2 : ∀ i : Fin 2 × ℕ × ℕ × ℕ, 0 < i.1.1 + 3 * i.2.1 → 2 ≤ i.2.2.1 →
      localEulerTerm R η U u v hv (p 0) (p 1) (p 2) i = 0) :
    ‖localEuler R η U u v hv (p 0) (p 1) (p 2) - 1‖ ≤
      16 * qI v.asIdeal ^ (-1 / 4000 : ℝ) := by
  classical
  let Q : ℝ := qI v.asIdeal
  let x : ℝ := (p 0).re
  let y : ℝ := (p 1).re
  let z : ℝ := (p 2).re
  let V : ℂ := localV v (p 2)
  let f : Fin 2 × ℕ × ℕ × ℕ → ℂ :=
    localEulerTerm R η U u v hv (p 0) (p 1) (p 2)
  change ‖(∑' i, f i) - 1‖ ≤ 16 * Q ^ (-1 / 4000 : ℝ)
  change ∀ m, f (0, 0, 0, m) = V ^ m at hVtail
  change f (0, 0, 0, 0) = 1 at hbase
  change ∀ k m, k ≠ 0 → f (0, 0, k, m) = 0 at ht0
  have hr : 1 / 2 - x ≤ -1 / 4000 ∧ 2 - 3 * x ≤ -1 / 1000 ∧
      2 - 3 * x ≤ -1 / 4000 ∧
      2 - 3 * x + (1 / 2 - y) ≤ -1 / 4000 ∧
      1 - x - y ≤ -1 / 4000 ∧ -6 * z ≤ -1 / 4000 - 1 / 1000 := by
    change (998 / 1000 - 1 / 100000 < x ∧ 3 / 1000 - 1 / 100000 < y ∧
      4 / 10 - 1 / 100000 < z) ∨
      (998 / 1000 - 1 / 100000 < x ∧ 95 / 100 - 1 / 100000 < y ∧
      16 / 100 - 1 / 100000 < z) at hp
    rcases hp with ⟨hx, hy, hz⟩ | ⟨hx, hy, hz⟩ <;>
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [hx, hy, hz]
  obtain ⟨ha, hb, hb0, hbc, hac, hz⟩ := hr
  have hQone : 1 < Q := lt_trans (one_lt_pow₀ (by norm_num : (1 : ℝ) < 2) (by decide : (2000 : ℕ) ≠ 0)) hQ
  have hQpos : 0 < Q := lt_trans zero_lt_one hQone
  have hVnorm : ‖V‖ ≤ Q ^ (-6 * z) := by
    dsimp [V, localV]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQpos]
    simp [z, Complex.mul_re]
  have hroot : 4 < Q ^ (1 / 1000 : ℝ) := by
    calc
      4 = ((2 : ℝ) ^ (2000 : ℕ)) ^ (1 / 1000 : ℝ) := by
        rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
      _ < _ := Real.rpow_lt_rpow (by positivity) hQ (by norm_num)
  have hsmall : Q ^ (-1 / 1000 : ℝ) ≤ 1 / 4 := by
    calc
      Q ^ (-1 / 1000 : ℝ) = (Q ^ (1 / 1000 : ℝ))⁻¹ := by
        rw [show (-1 / 1000 : ℝ) = -(1 / 1000 : ℝ) by ring, Real.rpow_neg hQpos.le]
      _ ≤ (4 : ℝ)⁻¹ := (inv_le_inv₀ (Real.rpow_pos_of_pos hQpos _) (by norm_num)).2 hroot.le
      _ = 1 / 4 := by norm_num
  let t : ℝ := Q ^ (-1 / 4000 : ℝ)
  let r : ℝ := 1 / 4
  have ht : 0 ≤ t := Real.rpow_nonneg hQpos.le _
  have hgeom (n m : ℕ) (a : ℝ)
      (h : a ≤ -1 / 4000 - (n : ℝ) / 1000 - (m : ℝ) / 1000) :
      Q ^ a ≤ t * r ^ n * r ^ m := by
    calc
      Q ^ a ≤ Q ^ (-1 / 4000 - (n : ℝ) / 1000 - (m : ℝ) / 1000) :=
        Real.rpow_le_rpow_of_exponent_le hQone.le h
      _ = t * (Q ^ (-1 / 1000 : ℝ)) ^ n * (Q ^ (-1 / 1000 : ℝ)) ^ m := by
        rw [← Real.rpow_mul_natCast hQpos.le, ← Real.rpow_mul_natCast hQpos.le,
          ← Real.rpow_add hQpos, ← Real.rpow_add hQpos]
        congr 1; ring
      _ ≤ t * r ^ n * r ^ m := by dsimp [r]; gcongr
  let L : ℕ → ℝ := fun l => if l = 0 then 1 else r ^ (l - 1)
  let K : ℕ → ℝ := fun k => if k < 2 then 1 else 0
  let M : ℕ → ℝ := fun m => r ^ m
  have hLn (n : ℕ) : 0 ≤ L n := by simp only [L]; split_ifs <;> positivity
  have hKn (n : ℕ) : 0 ≤ K n := by simp only [K]; split_ifs <;> positivity
  have hMn (n : ℕ) : 0 ≤ M n := by dsimp [M, r]; positivity
  have hMs : HasSum M (4 / 3 : ℝ) := by
    convert hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num : (1 / 4 : ℝ) < 1) using 1 <;> norm_num [M, r]
  have hLs : HasSum L (7 / 3 : ℝ) := by
    apply (hasSum_nat_add_iff' 1).mp
    have hshift : (fun n => L (n + 1)) = M := by funext n; simp [L, M]
    rw [hshift]
    norm_num [L]
    exact hMs
  have hKs : HasSum K (2 : ℝ) := by
    have heq : K = fun k : ℕ => (if k = 0 then 1 else 0) + (if k = 1 then 1 else 0) := by
      funext k
      by_cases h0 : k = 0
      · simp [K, h0]
      by_cases h1 : k = 1
      · simp [K, h1]
      have h2 : ¬k < 2 := by omega
      simp only [K, if_neg h2, if_neg h0, if_neg h1, add_zero]
    rw [heq]
    convert (hasSum_ite_eq (0 : ℕ) (1 : ℝ)).add (hasSum_ite_eq (1 : ℕ) (1 : ℝ)) using 1 <;> norm_num
  have hKM : Summable (fun km : ℕ × ℕ => K km.1 * M km.2) :=
    hKs.summable.mul_of_nonneg hMs.summable hKn hMn
  have hLKM : Summable (fun lkm : ℕ × ℕ × ℕ => L lkm.1 * (K lkm.2.1 * M lkm.2.2)) :=
    hLs.summable.mul_of_nonneg hKM hLn (fun km => mul_nonneg (hKn km.1) (hMn km.2))
  have hfin : Summable (fun _ : Fin 2 => t) := Summable.of_finite
  let g : Fin 2 × ℕ × ℕ × ℕ → ℝ := fun i => t * (L i.2.1 * (K i.2.2.1 * M i.2.2.2))
  have hgs : Summable g := hfin.mul_of_nonneg hLKM (fun _ => ht)
    (fun lkm => mul_nonneg (hLn lkm.1) (mul_nonneg (hKn lkm.2.1) (hMn lkm.2.2)))
  have hgn (i) : 0 ≤ g i :=
    mul_nonneg ht (mul_nonneg (hLn i.2.1) (mul_nonneg (hKn i.2.2.1) (hMn i.2.2.2)))
  have hgsum : ∑' i, g i = (112 / 9) * t := by
    rw [← hfin.tsum_mul_tsum hLKM hgs, ← hLs.summable.tsum_mul_tsum hKM hLKM,
      ← hKs.summable.tsum_mul_tsum hMs.summable hKM, hKs.tsum_eq, hMs.tsum_eq, hLs.tsum_eq]
    simp only [tsum_fintype, Fin.sum_univ_two]; ring
  let f0 : Fin 2 × ℕ × ℕ × ℕ → ℂ := fun i => if i = (0, 0, 0, 0) then 0 else f i
  have hfs : Summable (fun i => ‖f0 i‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ hs
    intro i
    by_cases hi : i = (0, 0, 0, 0)
    · simpa only [f0, if_pos hi, norm_zero] using norm_nonneg (f i)
    · simpa only [f0, if_neg hi] using (le_rfl : ‖f i‖ ≤ ‖f i‖)
  have hbound (i : Fin 2 × ℕ × ℕ × ℕ) : ‖f0 i‖ ≤ g i := by
    by_cases hi : i = (0, 0, 0, 0)
    · simp only [f0, if_pos hi, norm_zero]; exact hgn i
    rw [show f0 i = f i by simp [f0, hi]]
    obtain ⟨e, l, k, m⟩ := i
    by_cases hk : k ≤ 1
    · have hK : K k = 1 := by simp only [K, if_pos (show k < 2 by omega)]
      cases l with
      | zero =>
        fin_cases e
        · change ‖f (0, 0, k, m)‖ ≤ g (0, 0, k, m)
          by_cases hk0 : k = 0
          · subst k
            have hm : 1 ≤ m := by
              by_contra h
              have hm0 : m = 0 := by omega
              subst m; exact hi rfl
            rw [hVtail, norm_pow]
            calc
              ‖V‖ ^ m ≤ (Q ^ (-6 * z)) ^ m := pow_le_pow_left₀ (norm_nonneg _) hVnorm _
              _ = Q ^ ((-6 * z) * (m : ℝ)) := (Real.rpow_mul_natCast hQpos.le _ _).symm
              _ ≤ t * r ^ 0 * r ^ m := hgeom 0 m _ (by
                have hmc : 1 ≤ (m : ℝ) := by exact_mod_cast hm
                nlinarith [mul_le_mul_of_nonneg_right hz (Nat.cast_nonneg m)])
              _ = g (0, 0, 0, m) := by simp [g, L, K, M]
          · rw [ht0 k m hk0, norm_zero]; exact hgn _
        · change ‖f (1, 0, k, m)‖ ≤ g (1, 0, k, m)
          have hh := hsharp (1, 0, k, m) (by norm_num) hk
          refine hh.trans ?_
          calc
            _ ≤ t * r ^ 0 * r ^ m := hgeom 0 m _ (by
              have hm := mul_le_mul_of_nonneg_right (show -6 * z ≤ -1 / 1000 by linarith only [hz]) (Nat.cast_nonneg m)
              have hk0 : k = 0 ∨ k = 1 := by omega
              rcases hk0 with rfl | rfl <;> simp only [Fin.val_one, Nat.cast_one, Nat.cast_zero] <;> nlinarith)
            _ = g (1, 0, k, m) := by simp [g, L, hK, M]
      | succ n =>
        have hh := hsharp (e, n + 1, k, m) (by simp) hk
        refine hh.trans ?_
        calc
          _ ≤ t * r ^ n * r ^ m := hgeom n m _ (by
            have he := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg e.val) (show 1 / 2 - x ≤ 0 by linarith only [ha])
            have hn := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg n)
            have hm := mul_le_mul_of_nonneg_right (show -6 * z ≤ -1 / 1000 by linarith only [hz]) (Nat.cast_nonneg m)
            have hk0 : k = 0 ∨ k = 1 := by omega
            rcases hk0 with rfl | rfl <;> simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] <;> nlinarith)
          _ = g (e, n + 1, k, m) := by simp [g, L, hK, M]; ring
    · have hkge : 2 ≤ k := by omega
      have hfzero : f (e, l, k, m) = 0 := by
        by_cases ht : 0 < e.val + 3 * l
        · exact hk2 _ ht hkge
        · have he : e = 0 := by apply Fin.ext; simp; omega
          have hl : l = 0 := by omega
          subst e; subst l; exact ht0 k m (by omega)
      rw [hfzero, norm_zero]; exact hgn _
  have hsum : ∑' i, f0 i = (∑' i, f i) - 1 := by
    calc
      _ = ∑' i, (f i - if i = (0, 0, 0, 0) then 1 else 0) := by
        apply tsum_congr
        intro i
        by_cases hi : i = (0, 0, 0, 0)
        · subst i; simp [f0, hbase]
        · simp [f0, hi]
      _ = _ := by
        rw [hs.of_norm.tsum_sub (hasSum_ite_eq (0, 0, 0, 0) (1 : ℂ)).summable]
        change (∑' i, f i) - (∑' i, if i = (0, 0, 0, 0) then (1 : ℂ) else 0) =
          (∑' i, f i) - 1
        rw [tsum_ite_eq]
  rw [← hsum]
  calc
    _ ≤ ∑' i, ‖f0 i‖ := norm_tsum_le_tsum_norm hfs
    _ ≤ ∑' i, g i := hfs.tsum_le_tsum hbound hgs
    _ = (112 / 9) * t := hgsum
    _ ≤ 16 * Q ^ (-1 / 4000 : ℝ) := by change (112 / 9) * t ≤ 16 * t; nlinarith

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
