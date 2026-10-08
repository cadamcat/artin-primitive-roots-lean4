import ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY.SieveAlgebra

/-!
Finite reindexing tools for the truncated rough-prime source sum.
-/

namespace ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY

open ArtinPrimitiveRoots.TypeII
open Classical

/-- Quotients of the members of `I` that are divisible by `d`. -/
noncomputable def divisorQuotients (I : Finset ℕ) (d : ℕ) : Finset ℕ :=
  (I.filter (fun m => d ∣ m)).image (fun m => m / d)

/-- Reindex a divisibility-restricted sum by writing every member as `d*h`. -/
theorem sum_filter_dvd_reindex (d : ℕ) (I : Finset ℕ)
    (f : ℕ → ℂ) :
    (∑ m ∈ I, (if d ∣ m then f m else 0)) =
      ∑ h ∈ divisorQuotients I d, f (d * h) := by
  classical
  let J : Finset ℕ := I.filter (fun m => d ∣ m)
  have hinj : Set.InjOn (fun m : ℕ => m / d) (↑J : Set ℕ) := by
    intro m hm n hn hmn
    have hmd : d ∣ m := (Finset.mem_filter.mp hm).2
    have hnd : d ∣ n := (Finset.mem_filter.mp hn).2
    have hmeq : d * (m / d) = m := Nat.mul_div_cancel' hmd
    have hneq : d * (n / d) = n := Nat.mul_div_cancel' hnd
    change m / d = n / d at hmn
    calc
      m = d * (m / d) := hmeq.symm
      _ = d * (n / d) := by rw [hmn]
      _ = n := hneq
  calc
    (∑ m ∈ I, (if d ∣ m then f m else 0)) = ∑ m ∈ J, f m := by
      rw [← Finset.sum_filter]
    _ = ∑ m ∈ J, f (d * (m / d)) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmd : d ∣ m := (Finset.mem_filter.mp hm).2
      rw [Nat.mul_div_cancel' hmd]
    _ = ∑ h ∈ divisorQuotients I d, f (d * h) := by
      dsimp [divisorQuotients]
      exact (Finset.sum_image (f := fun h => f (d * h)) hinj).symm

end ArtinPrimitiveRoots.TypeII.Proofs.R_PROXY
