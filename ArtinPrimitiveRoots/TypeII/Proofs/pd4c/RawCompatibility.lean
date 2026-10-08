import ArtinPrimitiveRoots.TypeII.Proofs.pd4c.RawActualEndpoint

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd4d_sol

open Classical ArtinPrimitiveRoots.TypeII ArtinPrimitiveRoots.TypeII.PD

noncomputable section

/-- A nonzero admissible raw edge supplies the fixed-anchor compatibility data. -/
theorem raw_edge_compatible {K : ℕ} (F : PDFix K) (S : PDScale)
    (s : MemPoint S.x K) (σ : Fin K → Equiv.Perm (Fin (slotCount S.x)))
    (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i)
    (I : Finset (Fin K)) (iStar : Fin K) (hstar : iStar ∈ I)
    (k : Fin (s.2.2 iStar).length) (hk : (c iStar).2 = Sum.inl k)
    (fresh : Fin K → ℕ) (hfresh : ∀ i, i ∉ I → fresh i = edgeNewLabel (c i))
    (w : ArchRoot) (forward : Bool) (z' : ℤ × ℤ)
    (hadm : EdgeAdmissible F S w (s.1, permuteLists σ s.2.1, s.2.2) c z')
    (hraw : edgeMultiplier F S forward true (permuteLists σ s.2.1)
      (edgeTargetLists F S (s.1, permuteLists σ s.2.1, s.2.2) c) s.1 z' ≠ 0) :
    RawAnchorCompatible S F.a s.2.1 I iStar fresh w
      ((s.2.2 iStar).get k) s.1 (fun i => σ i (lastSlot S.x)) := by
  exact ⟨fun i => edgeNewLabel (c i), z',
    raw_edge_endpoint F S s σ c I iStar hstar k hk fresh hfresh w forward z' hadm hraw⟩

end

end ArtinPrimitiveRoots.Proofs.pd4d_sol
