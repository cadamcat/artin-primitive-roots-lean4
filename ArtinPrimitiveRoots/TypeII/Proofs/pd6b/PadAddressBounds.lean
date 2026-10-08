import ArtinPrimitiveRoots.TypeII.Proofs.pd6b.PadProbability

set_option autoImplicit false
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical

/-- Same-group pad collisions have at most KJ² ordered address pairs. -/
theorem padAddressPairs_card_le (x : ℝ) (K : ℕ) :
    (padAddressPairs x K).card ≤ K * (momentJ x) ^ 2 := by
  let key (q : (Fin K × Fin (momentJ x)) × (Fin K × Fin (momentJ x))) :
      Fin K × (Fin (momentJ x) × Fin (momentJ x)) :=
    (q.1.1, (q.1.2, q.2.2))
  have hinj : (↑(padAddressPairs x K) : Set _).InjOn key := by
    intro q hq q' hq' hk
    have hg := (Finset.mem_filter.mp hq).2.1
    have hg' := (Finset.mem_filter.mp hq').2.1
    change (q.1.1, (q.1.2, q.2.2)) = (q'.1.1, (q'.1.2, q'.2.2)) at hk
    rcases q with ⟨⟨i, j⟩, ⟨l, m⟩⟩
    rcases q' with ⟨⟨i', j'⟩, ⟨l', m'⟩⟩
    change (i, (j, m)) = (i', (j', m')) at hk
    have hii : i = i' := congrArg (fun t : Fin K × (Fin (momentJ x) × Fin (momentJ x)) => t.1) hk
    have hjj : j = j' := congrArg (fun t : Fin K × (Fin (momentJ x) × Fin (momentJ x)) => t.2.1) hk
    have hmm : m = m' := congrArg (fun t : Fin K × (Fin (momentJ x) × Fin (momentJ x)) => t.2.2) hk
    have hll : l = l' := hg.symm.trans (hii.trans hg')
    exact Prod.ext (Prod.ext hii hjj) (Prod.ext hll hmm)
  have hcard := Finset.card_image_of_injOn hinj
  have hb := Finset.card_le_univ ((padAddressPairs x K).image key)
  rw [hcard] at hb
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two, mul_assoc] using hb

end ArtinPrimitiveRoots.TypeII.PD
