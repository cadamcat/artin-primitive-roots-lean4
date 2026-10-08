import ArtinPrimitiveRoots.Proofs.pd_life_b.GhostSubsetSumPi
import ArtinPrimitiveRoots.Proofs.pd_life_b.HistoryPermutation

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace ArtinPrimitiveRoots.Proofs.pd_lifeb_sol

open Classical
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII

noncomputable section

/-- A ghost output using the canonical list of each finite birth subset. -/
def subsetGhostPoint {K : ℕ} (F : PDFix K) (S : PDScale) (j : ℕ)
    (σ : LogPoint S.x K)
    (D : (i : Fin K) → Finset (Fin (σ.1.2.2 i).length))
    (T : (i : Fin K) → (primeBand S.x (F.a i)).powerset) : LogPoint S.x K :=
  ((σ.1.1, σ.1.2.1, fun i => removeIndices (σ.1.2.2 i) (D i) ++
      ((T i).1.toList.map fun p => anchorAt p σ.1.1)),
    σ.2 ++ (List.finRange K).flatMap fun i =>
      ((T i).1.toList.zipIdx.map fun b => (BirthAddress.ghost j i b.2, b.1)))

/-- A continuation that kills repeated births turns the ghost operator into a finite sum
over deletion indices and band-subset births, with its literal signed weights retained. -/
theorem logGhost_eq_subset_batches {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) (f : LogPoint S.x K → ℂ)
    (hf : RespectsLoggedPerm f)
    (hbad : ∀ σ, ¬ (σ.2.map Prod.snd).Nodup → f σ = 0)
    (σ : LogPoint S.x K) :
    logGhost F S ρ j f σ =
      ∑ D : (i : Fin K) → Finset (Fin (σ.1.2.2 i).length),
        ∑ T : (i : Fin K) → (primeBand S.x (F.a i)).powerset,
          if ∀ i, D i ⊆ hitIndices (σ.1.2.2 i) σ.1.1 then
            ((∏ i : Fin K,
                (-memoryEta S.x F.q_d j / ρ) ^ (D i).card *
                (memoryQ S.x F.q_d j / ρ ^ 2) ^
                  (hitCount (σ.1.2.2 i) σ.1.1 - (D i).card) *
                (-memoryEta S.x F.q_d j * bandMass S.x (F.a i) / ρ) ^ (T i).1.card *
                (∏ p ∈ (T i).1, memoryNu S.x K F.a F.q_d i p) : ℝ) : ℂ) *
              f (subsetGhostPoint F S j σ D T)
          else 0 := by
  classical
  let U (i : Fin K) := primeBand S.x (F.a i)
  let ν (i : Fin K) (p : ℕ) := memoryNu S.x K F.a F.q_d i p
  let a (i : Fin K) := -memoryEta S.x F.q_d j * bandMass S.x (F.a i) / ρ
  let deletion (D : (i : Fin K) → Finset (Fin (σ.1.2.2 i).length)) (i : Fin K) : ℝ :=
    (-memoryEta S.x F.q_d j / ρ) ^ (D i).card *
      (memoryQ S.x F.q_d j / ρ ^ 2) ^ (hitCount (σ.1.2.2 i) σ.1.1 - (D i).card)
  let C (D : (i : Fin K) → Finset (Fin (σ.1.2.2 i).length)) : ℝ := ∏ i, deletion D i
  let out (D : (i : Fin K) → Finset (Fin (σ.1.2.2 i).length))
      (b : Fin K → List ℕ) : LogPoint S.x K :=
    ((σ.1.1, σ.1.2.1, fun i => removeIndices (σ.1.2.2 i) (D i) ++
        (b i).map (fun p => anchorAt p σ.1.1)),
      σ.2 ++ (List.finRange K).flatMap fun i =>
        ((b i).zipIdx.map fun e => (BirthAddress.ghost j i e.2, e.1)))
  let batches (l : Fin K → ℕ) (new : (i : Fin K) → Fin (l i) → U i) : Fin K → List ℕ :=
    fun i => List.ofFn fun k => (new i k).1
  let raw (D : (i : Fin K) → Finset (Fin (σ.1.2.2 i).length))
      (l : Fin K → ℕ) (new : (i : Fin K) → Fin (l i) → U i) : LogPoint S.x K :=
    ((σ.1.1, σ.1.2.1, fun i => removeIndices (σ.1.2.2 i) (D i) ++
        List.ofFn (fun k => anchorAt (new i k) σ.1.1)),
      σ.2 ++ (List.finRange K).flatMap fun i =>
        List.ofFn fun k : Fin (l i) => (BirthAddress.ghost j i k.val, (new i k : ℕ)))
  have hOutLog (D) (b : Fin K → List ℕ) :
      (out D b).2.map Prod.snd = σ.2.map Prod.snd ++ (List.finRange K).flatMap b := by
    simp only [out, List.map_append, List.map_flatMap, List.map_map]
    congr 1
    apply congrArg (List.finRange K).flatMap
    funext i
    change (b i).zipIdx.map Prod.fst = b i
    exact List.zipIdx_map_fst 0 (b i)
  have hRawLog (D) (l : Fin K → ℕ) (new : (i : Fin K) → Fin (l i) → U i) :
      (raw D l new).2.map Prod.snd =
        σ.2.map Prod.snd ++ (List.finRange K).flatMap (batches l new) := by
    simp only [raw, batches, List.map_append, List.map_flatMap, List.map_ofFn,
      Function.comp_def]
  have hRawValue (D) (l : Fin K → ℕ) (new : (i : Fin K) → Fin (l i) → U i) :
      f (raw D l new) = f (out D (batches l new)) := by
    apply hf
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro i
      change (removeIndices (σ.1.2.2 i) (D i) ++ _).Perm
        (removeIndices (σ.1.2.2 i) (D i) ++ (List.ofFn fun k => (new i k).1).map
          (fun p => anchorAt p σ.1.1))
      rw [List.map_ofFn]
      exact List.Perm.refl _
    · rw [hRawLog, hOutLog]
  have hInvariant (D) (b c : Fin K → List ℕ) (hbc : ∀ i, (b i).Perm (c i)) :
      f (out D b) = f (out D c) := by
    apply hf
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro i
      exact (List.Perm.refl _).append ((hbc i).map (fun p => anchorAt p σ.1.1))
    · rw [hOutLog, hOutLog]
      exact (List.Perm.refl _).append
        (List.Perm.flatMap_left (List.finRange K) (fun i _ => hbc i))
  have hInjective (D) (l : Fin K → ℕ) (new : (i : Fin K) → Fin (l i) → U i)
      (hnd : ((raw D l new).2.map Prod.snd).Nodup) :
      ∀ i, Function.Injective (new i) := by
    rw [hRawLog] at hnd
    have hflat := List.Nodup.of_append_right hnd
    intro i
    have hi := (List.nodup_flatMap.mp hflat).1 i (List.mem_finRange i)
    have hinj : Function.Injective (fun k => (new i k).1) := List.nodup_ofFn.mp hi
    intro k k' heq
    exact hinj (congrArg Subtype.val heq)
  have hCoeff (D) (l : Fin K → ℕ) (new : (i : Fin K) → Fin (l i) → U i) :
      (∏ i : Fin K, ghostGroupCoeff F S ρ j i (hitCount (σ.1.2.2 i) σ.1.1)
        (D i).card (l i) (batches l new i)) =
        C D * ∏ i : Fin K, (a i ^ l i * ∏ k, ν i (new i k).1) / ((l i).factorial : ℝ) := by
    calc
      _ = ∏ i : Fin K, deletion D i *
            ((a i ^ l i * ∏ k, ν i (new i k).1) / ((l i).factorial : ℝ)) := by
        apply Finset.prod_congr rfl
        intro i _
        simp only [ghostGroupCoeff, batches, List.map_ofFn, List.prod_ofFn, Function.comp_def,
          deletion, a, ν]
        ring
      _ = _ := Finset.prod_mul_distrib
  unfold logGhost
  dsimp only
  apply Finset.sum_congr rfl
  intro D _
  by_cases hD : ∀ i, D i ⊆ hitIndices (σ.1.2.2 i) σ.1.1
  · simp only [ite_eq_left hD]
    let g : (Fin K → List ℕ) → ℂ := fun b => (C D : ℂ) * f (out D b)
    have hg : ∀ b c, (∀ i, (b i).Perm (c i)) → g b = g c := by
      intro b c hbc
      dsimp only [g]
      rw [hInvariant D b c hbc]
    calc
      _ = ∑' l : Fin K → ℕ, ∑ new : (i : Fin K) → Fin (l i) → U i,
            if ∀ i, Function.Injective (new i) then
              ((∏ i : Fin K, (a i ^ l i * ∏ k, ν i (new i k).1) /
                ((l i).factorial : ℝ) : ℝ) : ℂ) * g (batches l new)
            else 0 := by
        apply tsum_congr
        intro l
        apply Finset.sum_congr rfl
        intro new _
        by_cases hinj : ∀ i, Function.Injective (new i)
        · rw [ite_eq_left hinj]
          change ((∏ i : Fin K, ghostGroupCoeff F S ρ j i
            (hitCount (σ.1.2.2 i) σ.1.1) (D i).card (l i) (batches l new i) : ℝ) : ℂ) *
              f (raw D l new) = _
          rw [hCoeff, Complex.ofReal_mul, hRawValue]
          dsimp only [g]
          ring
        · rw [ite_eq_right hinj]
          have hz : f (raw D l new) = 0 :=
            hbad _ (fun hnd => hinj (hInjective D l new hnd))
          change _ * f (raw D l new) = 0
          rw [hz, mul_zero]
      _ = ∑ T : (i : Fin K) → (U i).powerset,
            ((∏ i : Fin K, a i ^ (T i).1.card * ∏ p ∈ (T i).1, ν i p : ℝ) : ℂ) *
              g (fun i => (T i).1.toList) :=
        ghost_birth_subset_sum_pi K U ν a g hg
      _ = _ := by
        apply Finset.sum_congr rfl
        intro T _
        have hScalar :
            (∏ i : Fin K,
                (-memoryEta S.x F.q_d j / ρ) ^ (D i).card *
                (memoryQ S.x F.q_d j / ρ ^ 2) ^
                  (hitCount (σ.1.2.2 i) σ.1.1 - (D i).card) *
                (-memoryEta S.x F.q_d j * bandMass S.x (F.a i) / ρ) ^ (T i).1.card *
                (∏ p ∈ (T i).1, memoryNu S.x K F.a F.q_d i p) : ℝ) =
              C D * ∏ i : Fin K, a i ^ (T i).1.card * ∏ p ∈ (T i).1, ν i p := by
          simp only [C, deletion, a, ν, Finset.prod_mul_distrib]
          ring
        rw [hScalar, Complex.ofReal_mul]
        change _ * ((C D : ℂ) * f (subsetGhostPoint F S j σ D T)) = _
        ring
  · simp only [ite_eq_right hD, Finset.sum_const_zero, tsum_zero]

end

end ArtinPrimitiveRoots.Proofs.pd_lifeb_sol
