import ArtinPrimitiveRoots.TypeII.Proofs.pd2.Raw.RootFourierDiscrepancy

namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
set_option maxHeartbeats 1000000

lemma pd2a_pair_indicator {A B : Type*} [DecidableEq A] [DecidableEq B]
    (a c : A) (b d : B) :
    (if a = c then (1 : ℂ) else 0) * (if b = d then (1 : ℂ) else 0) =
      if (a, b) = (c, d) then 1 else 0 := by
  by_cases ha : a = c <;> by_cases hb : b = d <;> simp [Prod.mk.injEq, ha, hb]

lemma pd2a_density_count_identity (m ac Nc av Nv : ℕ)
    (G : Finset (ZMod m × ZMod m)) :
    (∑ z ∈ G, pd2a_rootIntervalDensity m ac Nc z.1 * pd2a_rootIntervalDensity m av Nv z.2) =
      (((((Finset.range Nc).product (Finset.range Nv)).filter (fun ij =>
        (((ac + ij.1 : ℕ) : ZMod m), ((av + ij.2 : ℕ) : ZMod m)) ∈ G)).card : ℕ) : ℂ) := by
  let p := fun i j : ℕ => (((ac + i : ℕ) : ZMod m), ((av + j : ℕ) : ZMod m))
  have hpoint : ∀ i j : ℕ,
      (∑ z ∈ G, (if ((ac + i : ℕ) : ZMod m) = z.1 then (1 : ℂ) else 0) *
        (if ((av + j : ℕ) : ZMod m) = z.2 then (1 : ℂ) else 0)) =
      if p i j ∈ G then 1 else 0 := by
    intro i j
    have hpair : ∀ z : ZMod m × ZMod m,
        (if ((ac + i : ℕ) : ZMod m) = z.1 then (1 : ℂ) else 0) *
        (if ((av + j : ℕ) : ZMod m) = z.2 then (1 : ℂ) else 0) =
        if p i j = z then 1 else 0 := fun z => pd2a_pair_indicator _ _ _ _
    simp_rw [hpair]
    by_cases hp : p i j ∈ G
    · rw [if_pos hp, Finset.sum_eq_single (p i j)]
      · simp
      · intro z hz hne
        rw [if_neg (Ne.symm hne)]
      · exact fun hn => (hn hp).elim
    · rw [if_neg hp]
      apply Finset.sum_eq_zero
      intro z hz
      have hNe : p i j ≠ z := by
        intro heq
        apply hp
        rw [heq]
        exact hz
      rw [if_neg hNe]
  have heq : (∑ z ∈ G, pd2a_rootIntervalDensity m ac Nc z.1 * pd2a_rootIntervalDensity m av Nv z.2) =
      ∑ i ∈ Finset.range Nc, ∑ j ∈ Finset.range Nv, if p i j ∈ G then (1 : ℂ) else 0 := by
    simp only [pd2a_rootIntervalDensity, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    exact hpoint i j
  rw [heq]
  rw [← Finset.sum_product (Finset.range Nc) (Finset.range Nv)
    (fun ij : ℕ × ℕ => if p ij.1 ij.2 ∈ G then (1 : ℂ) else 0)]
  rw [← Finset.sum_filter, Finset.sum_const]
  simp only [nsmul_eq_mul, mul_one]
  rfl

end ArtinPrimitiveRoots.TypeII.PD
