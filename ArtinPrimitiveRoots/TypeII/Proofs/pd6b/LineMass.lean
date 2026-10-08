import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadProbability

set_option autoImplicit false

namespace ArtinPrimitiveRoots.TypeII.PD

open ArtinPrimitiveRoots.TypeII Classical

noncomputable section

/-- Ordered prime labels in a union list, with an arbitrary common number of slots. -/
abbrev UnionLineChoice (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (N : ℕ) :=
  (q : Fin K × Fin N) → {p : ℕ // p ∈ primeBand x (a q.1)}

/-- Independent-line weight of a single selected prime. -/
def unionLineAtom (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (i : Fin K)
    (p : {p : ℕ // p ∈ primeBand x (a i)}) : ℝ :=
  (bandMass x (a i))⁻¹ * ((p.val : ℝ) + 1)⁻¹

/-- Independent-line weights charge each union label once. -/
def unionLineWeight (x : ℝ) {K : ℕ} (a : Fin K → ℝ) {N : ℕ}
    (t : UnionLineChoice x a N) : ℝ :=
  ∏ q : Fin K × Fin N, unionLineAtom x a q.1 (t q)

theorem unionLineAtom_nonneg {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (hV : ∀ i, 0 < bandMass x (a i)) (i : Fin K)
    (p : {p : ℕ // p ∈ primeBand x (a i)}) : 0 ≤ unionLineAtom x a i p := by
  unfold unionLineAtom
  have hi := hV i
  positivity

/-- A prescribed line has probability `1/(p+1)`, below the harmonic atom `1/p`. -/
theorem unionLineAtom_sum_le_one {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (hV : ∀ i, 0 < bandMass x (a i)) (i : Fin K) :
    (∑ p : {p : ℕ // p ∈ primeBand x (a i)}, unionLineAtom x a i p) ≤ 1 := by
  let V := bandMass x (a i)
  have hpos : 0 < V := hV i
  have hsum :
      (∑ p : {p : ℕ // p ∈ primeBand x (a i)},
        V⁻¹ * (p.val : ℝ)⁻¹) = 1 := by
    rw [← Finset.mul_sum]
    have hband :
        (∑ p : {p : ℕ // p ∈ primeBand x (a i)}, (p.val : ℝ)⁻¹) = V := by
      unfold V bandMass
      simpa only [one_div] using
        (Finset.sum_subtype (primeBand x (a i)) (fun _ => Iff.rfl)
          (fun p : ℕ => (p : ℝ)⁻¹)).symm
    rw [hband]
    exact inv_mul_cancel₀ hpos.ne'
  calc
    _ ≤ ∑ p : {p : ℕ // p ∈ primeBand x (a i)}, V⁻¹ * (p.val : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      have hpNat : p.val.Prime := (Finset.mem_filter.mp p.property).2.1
      have hpPos : 0 < (p.val : ℝ) := by exact_mod_cast hpNat.pos
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hpos.le)
      exact (inv_le_inv₀ (by positivity) hpPos).2 (by linarith)
    _ = 1 := hsum

/-- The unrestricted normalized one-edge union-label mass is at most one. -/
theorem unionLineWeight_sum_le_one {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (N : ℕ) (hV : ∀ i, 0 < bandMass x (a i)) :
    (∑ t : UnionLineChoice x a N, unionLineWeight x a t) ≤ 1 := by
  have hfactor :
      (∑ t : UnionLineChoice x a N, unionLineWeight x a t) =
        ∏ q : Fin K × Fin N,
          ∑ p : {p : ℕ // p ∈ primeBand x (a q.1)}, unionLineAtom x a q.1 p := by
    unfold unionLineWeight
    symm
    simpa only [Fintype.piFinset_univ] using
      (Finset.prod_univ_sum
        (fun q : Fin K × Fin N =>
          (Finset.univ : Finset {p : ℕ // p ∈ primeBand x (a q.1)}))
        (fun q p => unionLineAtom x a q.1 p))
  rw [hfactor]
  apply Finset.prod_le_one₀
  · intro q hq
    exact Finset.sum_nonneg (fun p _ => unionLineAtom_nonneg hV q.1 p)
  · intro q hq
    exact unionLineAtom_sum_le_one a hV q.1

/-- Restricting to compatible and distinct union lists can only decrease their mass. -/
theorem unionLineWeight_restricted_sum_le_one {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (N : ℕ) (hV : ∀ i, 0 < bandMass x (a i))
    (allowed : UnionLineChoice x a N → Prop) :
    (∑ t : UnionLineChoice x a N, if allowed t then unionLineWeight x a t else 0) ≤ 1 := by
  apply le_trans _ (unionLineWeight_sum_le_one a N hV)
  apply Finset.sum_le_sum
  intro t ht
  split_ifs
  · exact le_rfl
  · unfold unionLineWeight
    exact Finset.prod_nonneg (fun q _ => unionLineAtom_nonneg hV q.1 (t q))

end
end ArtinPrimitiveRoots.TypeII.PD
