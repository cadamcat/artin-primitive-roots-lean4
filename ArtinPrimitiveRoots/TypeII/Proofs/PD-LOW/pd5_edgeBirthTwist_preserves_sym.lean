import ArtinPrimitiveRoots.TypeII.Proofs.«PD-LOW».Defs
import ArtinPrimitiveRoots.Proofs.pd5_low_b.MemoryPermutation

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000
namespace ArtinPrimitiveRoots.TypeII.PD
open Classical
noncomputable section

/-- Promotion indices transport under source memory permutations; store flags, fresh labels
and birth logs are unchanged. Uses
MemoryPermutation, edgeNewMemory and symmetric continuations; feeds modified operation bounds. -/
theorem pd5_edgeBirthTwist_preserves_sym {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (j : ℕ) (W : BirthLog K → ℂ) (f : MemPoint S.x K → ℂ)
    (hf : IsMemorySymmetric f) :
    IsMemorySymmetric (pd5_edgeBirthTwist F S ρ w j W f) := by
  classical
  intro s τ
  let g : LogPoint S.x K → ℂ := logSym F S (fun p => W p.2 * f p.1)
  have hg (u v : MemPoint S.x K) (log : BirthLog K)
      (hpos : u.1 = v.1) (hactive : u.2.1 = v.2.1)
      (hmem : ∀ i, List.Perm (u.2.2 i) (v.2.2 i)) : g (v, log) = g (u, log) := by
    simp only [g, logSym]
    congr 1
    apply Fintype.sum_congr
    intro π
    have hstate :
        f (v.1, permuteLists π v.2.1, v.2.2) =
          f (u.1, permuteLists π u.2.1, u.2.2) := by
      apply memorySymmetric_eq_of_lists_perm f hf
        (u.1, permuteLists π u.2.1, u.2.2)
        (v.1, permuteLists π v.2.1, v.2.2)
      · exact hpos
      · simp [hactive]
      · exact hmem
    simp [hpos, hactive, hstate]
  have hpiece (r : MemPoint S.x K) (κ : MemoryPermutation r)
      (log : BirthLog K) (raw : Bool) (St Pr : Finset (Fin K)) :
      logEdgePiece F S ρ w j raw St Pr g (memoryPermute r κ, log) =
        logEdgePiece F S ρ w j raw St Pr g (r, log) := by
    let rt := memoryPermute r κ
    let e : (i : Fin K) → Fin (rt.2.2 i).length ≃ Fin (r.2.2 i).length := fun i =>
      (finCastEquiv (by simp [rt, memoryPermute])).trans (κ i)
    let CEquiv : (∀ i : Fin K, EdgeChoice S.x F.a (rt.2.2 i) i) ≃
        (∀ i : Fin K, EdgeChoice S.x F.a (r.2.2 i) i) :=
      Equiv.piCongrRight fun i =>
        Equiv.prodCongr (Equiv.refl Bool)
          (Equiv.sumCongr (e i) (Equiv.refl (primeBand S.x (F.a i))) )
    have hgetMem (i : Fin K) (k : Fin (rt.2.2 i).length) :
        (rt.2.2 i).get k = (r.2.2 i).get (e i k) := by
      have hlen : (List.ofFn fun q : Fin (r.2.2 i).length =>
          (r.2.2 i).get ((κ i) q)).length = (rt.2.2 i).length := by
        simp [rt, memoryPermute]
      change (List.ofFn fun q : Fin (r.2.2 i).length =>
          (r.2.2 i).get ((κ i) q)).get (Fin.cast hlen.symm k) =
        (r.2.2 i).get (e i k)
      rw [List.get_ofFn]
      congr 1
    have hinputPerm (i : Fin K) : List.Perm (rt.2.2 i) (r.2.2 i) := by
      simpa [rt, memoryPermute] using listPermute_perm (r.2.2 i) (κ i)
    have hlabel (c : ∀ i : Fin K, EdgeChoice S.x F.a (rt.2.2 i) i) (i : Fin K) :
        edgeNewLabel (c i) = edgeNewLabel (CEquiv c i) := by
      change edgeNewLabel (c i) = edgeNewLabel
        ((c i).1, Sum.map (e i) id (c i).2)
      cases hq : (c i).2 with
      | inl k =>
          simp only [edgeNewLabel, hq, Sum.map_inl]
          exact congrArg Prod.fst (hgetMem i k)
      | inr p => simp [edgeNewLabel, hq]
    have htargetLists (c : ∀ i : Fin K, EdgeChoice S.x F.a (rt.2.2 i) i) :
        edgeTargetLists F S rt c = edgeTargetLists F S r (CEquiv c) := by
      funext i jj
      by_cases h : jj.val < momentJ S.x
      · simp [edgeTargetLists, rt, memoryPermute, h]
      · simp only [edgeTargetLists, rt, memoryPermute, if_neg h]
        exact hlabel c i
    have hbirths (c : ∀ i : Fin K, EdgeChoice S.x F.a (rt.2.2 i) i) :
        edgeBirths F S j rt c = edgeBirths F S j r (CEquiv c) := by
      unfold edgeBirths
      apply List.flatMap_congr
      intro i hi
      cases hq : (c i).2 <;> simp [CEquiv, hq]
    have hstored (c : ∀ i : Fin K, EdgeChoice S.x F.a (rt.2.2 i) i) :
        edgeStoredSet c = edgeStoredSet (CEquiv c) := by
      ext i
      simp [edgeStoredSet, CEquiv]
    have hpromoted (c : ∀ i : Fin K, EdgeChoice S.x F.a (rt.2.2 i) i) :
        edgePromotedSet c = edgePromotedSet (CEquiv c) := by
      ext i
      simp [edgePromotedSet, CEquiv]
    have hmemPerm (c : ∀ i : Fin K, EdgeChoice S.x F.a (rt.2.2 i) i) (i : Fin K) :
        List.Perm (edgeNewMemory F S rt c i) (edgeNewMemory F S r (CEquiv c) i) := by
      let Dtar : Finset (Fin (rt.2.2 i).length) :=
        match (c i).2 with
        | Sum.inl k => {k}
        | Sum.inr _ => ∅
      let Dsrc : Finset (Fin (r.2.2 i).length) :=
        match (CEquiv c i).2 with
        | Sum.inl k => {k}
        | Sum.inr _ => ∅
      have hDsrc : Dsrc = Dtar.image (e i) := by
        cases hq : (c i).2 <;> simp [Dsrc, Dtar, CEquiv, hq]
      obtain ⟨D', hrel, hcard', hdel⟩ :=
        removeIndices_reindex_perm (r.2.2 i) (κ i) Dsrc
      have hD' : D' = Dtar := by
        ext k
        rw [hrel, hDsrc]
        simp [Dtar, e, finCastEquiv]
        constructor
        · rintro ⟨a, ha, hak⟩
          have haval : a.val = k.val := by
            have hval := congrArg Fin.val hak
            simpa using hval
          exact (Fin.ext haval) ▸ ha
        · intro hk
          exact ⟨k, hk, by apply Fin.ext; rfl⟩
      rw [hD'] at hdel
      have hstore : (CEquiv c i).1 = (c i).1 := by simp [CEquiv]
      have hsuffix :
          (if (c i).1 then [anchorAt (rt.2.1 i (lastSlot S.x)) rt.1] else []) =
            (if (CEquiv c i).1 then [anchorAt (r.2.1 i (lastSlot S.x)) r.1] else []) := by
        rw [hstore]
        simp [rt, memoryPermute]
      change List.Perm
        (removeIndices (rt.2.2 i) Dtar ++
          (if (c i).1 then [anchorAt (rt.2.1 i (lastSlot S.x)) rt.1] else []))
        (removeIndices (r.2.2 i) Dsrc ++
          (if (CEquiv c i).1 then [anchorAt (r.2.1 i (lastSlot S.x)) r.1] else []))
      rw [hsuffix]
      exact hdel.append_right
        (if (CEquiv c i).1 then [anchorAt (r.2.1 i (lastSlot S.x)) r.1] else [])
    unfold logEdgePiece
    apply Fintype.sum_equiv CEquiv
    intro c
    apply tsum_congr
    intro z'
    have hadm : EdgeAdmissible F S w rt c z' ↔
        EdgeAdmissible F S w r (CEquiv c) z' := by
      have hprom :
          (∀ i, ∀ k, (c i).2 = Sum.inl k → particleHits ((rt.2.2 i).get k) z') ↔
            (∀ i, ∀ k, (CEquiv c i).2 = Sum.inl k →
              particleHits ((r.2.2 i).get k) z') := by
        constructor
        · intro h i k hk
          have hmap : Sum.map (e i) id (c i).2 = Sum.inl k := by
            simpa [CEquiv] using hk
          cases hq : (c i).2 with
          | inl q =>
              have heq : e i q = k := by simpa [hq] using hmap
              have hq' : q = (e i).symm k := by
                calc
                  q = (e i).symm (e i q) := by simp
                  _ = (e i).symm k := congrArg (e i).symm heq
              have hfill : (c i).2 = Sum.inl ((e i).symm k) := by simpa [hq'] using hq
              have hout := h i ((e i).symm k) hfill
              have hget := hgetMem i ((e i).symm k)
              rw [(e i).apply_symm_apply k] at hget
              exact hget ▸ hout
          | inr p => simp [hq] at hmap
        · intro h i k hk
          have hfill : (CEquiv c i).2 = Sum.inl (e i k) := by
            simpa [CEquiv, hk]
          have hout := h i (e i k) hfill
          have hget := hgetMem i k
          exact hget.symm ▸ hout
      unfold EdgeAdmissible
      constructor
      · rintro ⟨hp, hrest⟩
        have hrest' := hrest
        rw [show rt.1 = r.1 from rfl, show rt.2.1 = r.2.1 from rfl,
          htargetLists c] at hrest'
        exact ⟨hprom.mp hp, hrest'⟩
      · rintro ⟨hp, hrest⟩
        have hrest' := hrest
        rw [show r.1 = rt.1 from rfl, show r.2.1 = rt.2.1 from rfl,
          (htargetLists c).symm] at hrest'
        exact ⟨hprom.mpr hp, hrest'⟩
    have hcond :
        (edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧ EdgeAdmissible F S w rt c z') ↔
          (edgeStoredSet (CEquiv c) = St ∧ edgePromotedSet (CEquiv c) = Pr ∧
            EdgeAdmissible F S w r (CEquiv c) z') := by
      simp [hstored c, hpromoted c, hadm]
    have holdHits :
        (∑ i : Fin K, hitCount (rt.2.2 i) rt.1) =
          (∑ i : Fin K, hitCount (r.2.2 i) r.1) := by
      apply Fintype.sum_congr
      intro i
      simpa [rt, memoryPermute] using (hitCount_perm (hinputPerm i).symm r.1)
    have hnewHits :
        (∑ i : Fin K, hitCount (edgeNewMemory F S rt c i) z') =
          (∑ i : Fin K, hitCount (edgeNewMemory F S r (CEquiv c) i) z') := by
      apply Fintype.sum_congr
      intro i
      exact (hitCount_perm (hmemPerm c i).symm z')
    have hmass :
        (∏ i : Fin K,
          match (c i).2 with
          | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
          | Sum.inr p => memoryNu S.x K F.a F.q_d i p) =
        (∏ i : Fin K,
          match (CEquiv c i).2 with
          | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
          | Sum.inr p => memoryNu S.x K F.a F.q_d i p) := by
      apply Fintype.prod_congr
      intro i
      cases hq : (c i).2 <;> simp [CEquiv, hq]
    have hcoeff :
        ρ ^ (∑ i : Fin K, hitCount (rt.2.2 i) rt.1) *
            (∏ i : Fin K,
              match (c i).2 with
              | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
              | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
            ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S rt c i) z') =
          ρ ^ (∑ i : Fin K, hitCount (r.2.2 i) r.1) *
            (∏ i : Fin K,
              match (CEquiv c i).2 with
              | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
              | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
            ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S r (CEquiv c) i) z') := by
      rw [holdHits, hmass, hnewHits]
    have hmult :
        edgeMultiplier F S (decide (j % 2 = 0)) raw rt.2.1
            (edgeTargetLists F S rt c) rt.1 z' =
          edgeMultiplier F S (decide (j % 2 = 0)) raw r.2.1
            (edgeTargetLists F S r (CEquiv c)) r.1 z' := by
      change edgeMultiplier F S (decide (j % 2 = 0)) raw r.2.1
          (edgeTargetLists F S rt c) r.1 z' =
        edgeMultiplier F S (decide (j % 2 = 0)) raw r.2.1
          (edgeTargetLists F S r (CEquiv c)) r.1 z'
      rw [htargetLists c]
    have hcoeff' :
        ρ ^ (∑ i : Fin K, hitCount ((memoryPermute r κ).2.2 i) (memoryPermute r κ).1) *
            (∏ i : Fin K,
              match (c i).2 with
              | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
              | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
            ρ ^ (∑ i : Fin K, hitCount
              (edgeNewMemory F S (memoryPermute r κ) c i) z') =
          ρ ^ (∑ i : Fin K, hitCount (r.2.2 i) r.1) *
            (∏ i : Fin K,
              match (CEquiv c i).2 with
              | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
              | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
            ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S r (CEquiv c) i) z') := by
      simpa [rt] using hcoeff
    have hmult' :
        edgeMultiplier F S (decide (j % 2 = 0)) raw (memoryPermute r κ).2.1
            (edgeTargetLists F S (memoryPermute r κ) c) (memoryPermute r κ).1 z' =
          edgeMultiplier F S (decide (j % 2 = 0)) raw r.2.1
            (edgeTargetLists F S r (CEquiv c)) r.1 z' := by
      simpa [rt] using hmult
    let qT : MemPoint S.x K :=
      (z', edgeTargetLists F S rt c, edgeNewMemory F S rt c)
    let qS : MemPoint S.x K :=
      (z', edgeTargetLists F S r (CEquiv c), edgeNewMemory F S r (CEquiv c))
    have hout :
        g (qT, log ++ edgeBirths F S j rt c) =
          g (qS, log ++ edgeBirths F S j r (CEquiv c)) := by
      rw [hbirths c]
      apply hg qS qT (log ++ edgeBirths F S j r (CEquiv c)) (by rfl)
        (htargetLists c).symm
      intro i
      exact (hmemPerm c i).symm
    by_cases hT : edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
        EdgeAdmissible F S w rt c z'
    · have hS : edgeStoredSet (CEquiv c) = St ∧ edgePromotedSet (CEquiv c) = Pr ∧
          EdgeAdmissible F S w r (CEquiv c) z' := hcond.mp hT
      have hT' : edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
          EdgeAdmissible F S w (memoryPermute r κ) c z' := by simpa [rt] using hT
      simp only [if_pos hT', if_pos hS]
      have hcastCoeff :
          (↑(ρ ^ (∑ i : Fin K, hitCount ((memoryPermute r κ).2.2 i) (memoryPermute r κ).1) *
            (∏ i : Fin K,
              match (c i).2 with
              | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
              | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
            ρ ^ (∑ i : Fin K, hitCount
              (edgeNewMemory F S (memoryPermute r κ) c i) z') : ℝ) : ℂ) =
          (↑(ρ ^ (∑ i : Fin K, hitCount (r.2.2 i) r.1) *
            (∏ i : Fin K,
              match (CEquiv c i).2 with
              | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
              | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
            ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S r (CEquiv c) i) z') : ℝ) : ℂ) :=
        congrArg (fun x : ℝ => (x : ℂ)) hcoeff'
      have hout' :
          g ((z', edgeTargetLists F S (memoryPermute r κ) c,
            edgeNewMemory F S (memoryPermute r κ) c),
              log ++ edgeBirths F S j (memoryPermute r κ) c) =
          g ((z', edgeTargetLists F S r (CEquiv c),
            edgeNewMemory F S r (CEquiv c)), log ++ edgeBirths F S j r (CEquiv c)) := by
        simpa [qT, qS, rt] using hout
      let coeffT : ℝ :=
        ρ ^ (∑ i : Fin K, hitCount ((memoryPermute r κ).2.2 i) (memoryPermute r κ).1) *
          (∏ i : Fin K,
            match (c i).2 with
            | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
            | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
          ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S (memoryPermute r κ) c i) z')
      let coeffS : ℝ :=
        ρ ^ (∑ i : Fin K, hitCount (r.2.2 i) r.1) *
          (∏ i : Fin K,
            match (CEquiv c i).2 with
            | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
            | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
          ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S r (CEquiv c) i) z')
      let multT := edgeMultiplier F S (decide (j % 2 = 0)) raw
        (memoryPermute r κ).2.1 (edgeTargetLists F S (memoryPermute r κ) c)
        (memoryPermute r κ).1 z'
      let multS := edgeMultiplier F S (decide (j % 2 = 0)) raw r.2.1
        (edgeTargetLists F S r (CEquiv c)) r.1 z'
      let valT := g ((z', edgeTargetLists F S (memoryPermute r κ) c,
        edgeNewMemory F S (memoryPermute r κ) c), log ++ edgeBirths F S j (memoryPermute r κ) c)
      let valS := g ((z', edgeTargetLists F S r (CEquiv c),
        edgeNewMemory F S r (CEquiv c)), log ++ edgeBirths F S j r (CEquiv c))
      have hcoeffCast : (↑coeffT : ℂ) = ↑coeffS := hcastCoeff
      have hmultCast : multT = multS := hmult'
      have hvalCast : valT = valS := by simpa [valT, valS, qT, qS, rt] using hout
      change (↑coeffT : ℂ) * multT * valT = (↑coeffS : ℂ) * multS * valS
      exact (congrArg (fun z : ℂ => z * multT * valT) hcoeffCast).trans
        ((congrArg (fun z : ℂ => (↑coeffS : ℂ) * z * valT) hmultCast).trans
          (congrArg (fun z : ℂ => (↑coeffS : ℂ) * multS * z) hvalCast))
    · have hS : ¬ (edgeStoredSet (CEquiv c) = St ∧ edgePromotedSet (CEquiv c) = Pr ∧
          EdgeAdmissible F S w r (CEquiv c) z') := fun h => hT (hcond.mpr h)
      have hT' : ¬ (edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
          EdgeAdmissible F S w (memoryPermute r κ) c z') := by simpa [rt] using hT
      simp [hT', hS]
  let H : LogPoint S.x K → ℂ := fun σL =>
    ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
      (logEdgePiece F S ρ w j true St Pr g σL -
        logEdgePiece F S ρ w j false St Pr g σL)
  change logSym F S H (memoryPermute s τ, []) = logSym F S H (s, [])
  simp only [logSym]
  congr 1
  apply Fintype.sum_congr
  intro π
  let r : MemPoint S.x K := (s.1, permuteLists π s.2.1, s.2.2)
  have hr :
      ((memoryPermute s τ).1,
        permuteLists π (memoryPermute s τ).2.1, (memoryPermute s τ).2.2) =
        memoryPermute r τ := by
    simp [r, memoryPermute]
  rw [hr]
  dsimp [H]
  simp_rw [hpiece r τ [] true, hpiece r τ [] false]
  simp [r]

end
end ArtinPrimitiveRoots.TypeII.PD
