import ArtinPrimitiveRoots.Proofs.pd_life_b.GuidedExistLift

set_option autoImplicit false

namespace ArtinPrimitiveRoots.Proofs.pd_birth_opus

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
open ArtinPrimitiveRoots.Proofs.pd_life_b

noncomputable section

/-- **Existence, terminal step.** -/
theorem exist_base {K : ℕ} (F : PDFix K) (S : PDScale) (w : ArchRoot) (γ : EnvPath S.x K)
    (hBands : ∀ i i' : Fin K, i ≠ i' →
      Disjoint (primeBand S.x (F.a i)) (primeBand S.x (F.a i')))
    (σ : LogPoint S.x K) (hR : ExistRec F S γ (Fin.last _) σ)
    (t : FiniteHistoryTrace F S γ 0 σ) (ht : FiniteHistoryTraceValid F S w γ 0 σ t) :
    ∃ H : PDLifeAssignment F S γ, IsLifeState F S γ H (Fin.last _) σ ∧
      TraceGuided F S γ H 0 σ t := by
  obtain ⟨-, hguard, ⟨-, hempty⟩, -⟩ := ht
  have hz : σ.1.1 = (γ (Fin.last _)).1 := congrArg Prod.fst hR.pos
  have hall : ∀ i (r : Fin (σ.1.2.2 i).length), r ∈ t.1 i := by
    intro i r
    by_contra hr
    have := (ghost_mem_iff F S (pathLength S.x) σ t i _).mpr (Or.inl ⟨r, hr, rfl⟩)
    rw [hempty i] at this
    simp at this
  have hT : ∀ i p, p ∉ (t.2 i).1 := by
    intro i p hp
    have := (ghost_mem_iff F S (pathLength S.x) σ t i (anchorAt p σ.1.1)).mpr (Or.inr ⟨hp, rfl⟩)
    rw [hempty i] at this
    simp at this
  have hle : ∀ m : Fin (pathLength S.x + 1), m ≤ Fin.last _ := fun m => Fin.le_last m
  have hlines : ∀ p m m', IsActiveAt γ p m → IsActiveAt γ p m' →
      projLine p (γ m).1 = projLine p (γ m').1 :=
    fun p m m' h h' => hR.actLine p m m' (hle m) (hle m') h h'
  have hex : ∀ i (p : primeBand S.x (F.a i)),
      ∃ e : PrimeLife S γ p.1, PrimeOK F S γ (Fin.last _) σ t i p e := by
    intro i p
    by_cases hmem : ∃ q ∈ σ.1.2.2 i, q.1 = p.1
    · obtain ⟨q, hq, hq1⟩ := hmem
      obtain ⟨r, hr⟩ := List.mem_iff_get.mp hq
      have huniq : ∀ q' ∈ σ.1.2.2 i, q'.1 = p.1 → q' = q := by
        intro q' hq' hq'1
        obtain ⟨r', hr'⟩ := List.mem_iff_get.mp hq'
        have : r' = r := index_inj_of_nodup _ (hR.memNodup i) r' r (by rw [hr', hr, hq'1, hq1])
        rw [← hr', ← hr, this]
      have hhit : q.2 = (projLine q.1 (γ (Fin.last _)).1).val := by
        have h := (Finset.mem_filter.mp (hguard i (hall i r))).2
        unfold particleHits at h
        rw [hr] at h; rw [h, hz]
      have hdeath : ∃ r ∈ t.1 i, ((σ.1.2.2 i).get r).1 = p.1 := ⟨r, hall i r, by rw [hr, hq1]⟩
      obtain ⟨hna, hrec⟩ := hR.memRec i q hq
      rw [hq1] at hna hhit
      rcases hrec with ⟨⟨a, ha, hla⟩, hno⟩ | ⟨m₀, hm₀, hact₀, hl₀⟩
      · rw [hq1] at hla hno
        have hA : ¬ (pdLifeActive S γ p.1).Nonempty := by
          rintro ⟨m, hm⟩
          exact hno m (hle m) ((mem_active_iff S γ p.1 m).mp hm)
        have hline : projLine p.1 (γ (Fin.last _)).1 = projLine p.1 (γ a).1 :=
          Fin.ext (by rw [← hhit, hla])
        refine ⟨⟨_, mkLife_inactive_some S γ p.1 hA a _ ha hline⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [pend_inactive_iff S γ p.1 _ hA]
          exact ⟨fun _ => ⟨q, hq, hq1⟩, fun _ => ⟨a, _, rfl, ha, le_rfl⟩⟩
        · intro q' hq' hq'1
          rw [huniq q' hq' hq'1]
          show q.2 = (lifeLine S γ p.1 (some a, some (Fin.last _))).val
          rw [lifeLine_inactive S γ p.1 a _ hA, ← hla]
        · intro _ _ _; rw [← hq1]; exact hR.memLog i q hq
        · intro _; exact Or.inr ⟨a, rfl, ha⟩
        · exact ⟨fun h => absurd (Option.some.inj h) (ne_of_lt ha), fun h => absurd h (hT i _)⟩
        · exact ⟨fun _ => hdeath, fun _ => rfl⟩
      · rw [hq1] at hact₀ hl₀
        have hA : (pdLifeActive S γ p.1).Nonempty := ⟨m₀, (mem_active_iff S γ p.1 m₀).mpr hact₀⟩
        have hvalid := mkLife_active S γ p.1 hA (hlines p.1) none (some (Fin.last _))
          (fun a h => by simp at h)
          (fun c hc => by
            cases hc
            refine ⟨fun m hm => lt_of_le_of_ne (hle m) (fun h => hna (h ▸ hm)), m₀, hact₀, ?_⟩
            exact Fin.ext (by rw [← hhit, hl₀]))
        refine ⟨⟨_, hvalid⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [pend_active_iff S γ p.1 _ hA]
          refine ⟨fun _ => ⟨q, hq, hq1⟩, fun _ => ⟨hna, Or.inr ?_, Or.inl ⟨_, rfl, le_rfl⟩⟩⟩
          exact lt_of_le_of_lt (Finset.min'_le _ _ ((mem_active_iff S γ p.1 m₀).mpr hact₀)) hm₀
        · intro q' hq' hq'1
          rw [huniq q' hq' hq'1]
          show q.2 = (lifeLine S γ p.1 (none, some (Fin.last _))).val
          rw [lifeLine_active S γ p.1 _ hA, ← hl₀,
            hlines p.1 m₀ _ hact₀ (Finset.mem_filter.mp (Finset.min'_mem _ hA)).2]
        · intro a h; simp at h
        · intro _; exact Or.inl ⟨m₀, hle m₀, hact₀⟩
        · exact ⟨fun h => by simp at h, fun h => absurd h (hT i _)⟩
        · exact ⟨fun _ => hdeath, fun _ => rfl⟩
    · push_neg at hmem
      have hnodeath : ¬ ∃ r ∈ t.1 i, ((σ.1.2.2 i).get r).1 = p.1 :=
        fun ⟨r, _, hr⟩ => hmem _ (List.get_mem _ r) hr
      have hnopend : ¬ ∃ q ∈ σ.1.2.2 i, q.1 = p.1 := fun ⟨q, hq, h⟩ => hmem q hq h
      by_cases hact : IsActiveAt γ p.1 (Fin.last _)
      · have hA : (pdLifeActive S γ p.1).Nonempty :=
          ⟨_, (mem_active_iff S γ p.1 _).mpr hact⟩
        have hvalid := mkLife_active S γ p.1 hA (hlines p.1) none none
          (fun a h => by simp at h) (fun c h => by simp at h)
        refine ⟨⟨_, hvalid⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [pend_active_iff S γ p.1 _ hA]
          exact ⟨fun h => absurd hact h.1, fun h => absurd h hnopend⟩
        · intro q hq h; exact absurd h (hmem q hq)
        · intro a h; simp at h
        · intro _; exact Or.inl ⟨_, le_rfl, hact⟩
        · exact ⟨fun h => by simp at h, fun h => absurd h (hT i _)⟩
        · exact ⟨fun h => by simp at h, fun h => absurd h hnodeath⟩
      by_cases hlog : p.1 ∈ σ.2.map Prod.snd
      · rcases hR.deadRec i p.1 p.2 hlog hmem hact with ⟨m₀, hm₀, hact₀⟩ |
          ⟨a, c, hac, hc, hl, hno⟩
        · have hA : (pdLifeActive S γ p.1).Nonempty :=
            ⟨m₀, (mem_active_iff S γ p.1 m₀).mpr hact₀⟩
          have hvalid := mkLife_active S γ p.1 hA (hlines p.1) none none
            (fun a h => by simp at h) (fun c h => by simp at h)
          refine ⟨⟨_, hvalid⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [pend_active_iff S γ p.1 _ hA]
            refine ⟨fun h => ?_, fun h => absurd h hnopend⟩
            rcases h.2.2 with ⟨c, hc, -⟩ | hω
            · simp at hc
            · exact absurd (hle _) (not_le.mpr hω)
          · intro q hq h; exact absurd h (hmem q hq)
          · intro a h; simp at h
          · intro _; exact Or.inl ⟨m₀, hle m₀, hact₀⟩
          · exact ⟨fun h => by simp at h, fun h => absurd h (hT i _)⟩
          · exact ⟨fun h => by simp at h, fun h => absurd h hnodeath⟩
        · have hA : ¬ (pdLifeActive S γ p.1).Nonempty := by
            rintro ⟨m, hm⟩
            exact hno m (hle m) ((mem_active_iff S γ p.1 m).mp hm)
          refine ⟨⟨_, mkLife_inactive_some S γ p.1 hA a c hac hl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [pend_inactive_iff S γ p.1 _ hA]
            constructor
            · rintro ⟨a', c', h, -, h2⟩
              simp only [Prod.mk.injEq, Option.some.injEq] at h
              rw [← h.2] at h2
              exact absurd hc (not_lt.mpr h2)
            · intro h; exact absurd h hnopend
          · intro q hq h; exact absurd h (hmem q hq)
          · intro _ _ _; exact hlog
          · intro _; exact Or.inr ⟨a, rfl, lt_trans hac hc⟩
          · exact ⟨fun h => absurd (Option.some.inj h) (ne_of_lt (lt_trans hac hc)),
              fun h => absurd h (hT i _)⟩
          · exact ⟨fun h => absurd (Option.some.inj h) (ne_of_lt hc), fun h => absurd h hnodeath⟩
      · have hA : ¬ (pdLifeActive S γ p.1).Nonempty := by
          rintro ⟨m, hm⟩
          exact hlog (hR.actLog p.1 m (hle m) ((mem_active_iff S γ p.1 m).mp hm))
        refine ⟨⟨_, mkLife_inactive_none S γ p.1 hA⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [pend_inactive_iff S γ p.1 _ hA]
          exact ⟨fun ⟨a, c, h, _⟩ => by simp at h, fun h => absurd h hnopend⟩
        · intro q hq h; exact absurd h (hmem q hq)
        · intro a h; simp at h
        · intro h; exact absurd h hlog
        · exact ⟨fun h => by simp at h, fun h => absurd h (hT i _)⟩
        · exact ⟨fun h => by simp at h, fun h => absurd h hnodeath⟩
  choose H hH using hex
  obtain ⟨hlife, hgg⟩ := lift_primeOK F S γ hBands H _ σ hR t hH
  exact ⟨H, hlife, hgg⟩

end

end ArtinPrimitiveRoots.Proofs.pd_birth_opus
