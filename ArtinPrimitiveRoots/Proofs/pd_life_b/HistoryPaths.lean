import ArtinPrimitiveRoots.TypeII.PD.Memory
import ArtinPrimitiveRoots.TypeII.Proofs.PD_LIFECYCLE.Defs
import ArtinPrimitiveRoots.Proofs.pd_life_b.BoundarySupport

set_option autoImplicit false
set_option linter.unusedVariables false

namespace ArtinPrimitiveRoots.Proofs.pd_life_b
open ArtinPrimitiveRoots.TypeII.PD
open ArtinPrimitiveRoots.TypeII
open Classical MeasureTheory Filter
noncomputable section

private theorem envPoint_band_box_finite {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (hU : 0 < S.U) (hV : 0 < S.V) (hw : w.InRegion S) :
    {s : EnvPoint S.x K | (∀ i j, s.2 i j ∈ primeBand S.x (F.a i)) ∧
      envBox S w s.1}.Finite := by
  classical
  rcases hw with ⟨huL, huR, hvL, hvR, hrL, hrU⟩
  have hu : 0 < w.u := lt_of_lt_of_le hU huL
  have hv : 0 < w.v := lt_of_lt_of_le hV hvL
  let M : ℝ := 16 + 500 * S.U * S.V
  let n : ℕ := ⌈M⌉₊
  have hM : 0 < M := by dsimp [M]; positivity
  have hn : M ≤ (n : ℝ) := by simpa [n] using (Nat.le_ceil M)
  have hUV : 0 < S.U * S.V := mul_pos hU hV
  let I : Set ℤ := Set.Icc (-(n : ℤ)) (n : ℤ)
  let Z : Set (ℤ × ℤ) := {z | envBox S w z}
  have hZsub : Z ⊆ I ×ˢ I := by
    intro z hz
    have hτlo' : S.U / w.u ≤ w.tau z := by
      apply (div_le_iff₀ hu).2
      simpa [mul_comm] using hz.1
    have hτlo : (1 / 16 : ℝ) ≤ w.tau z := by
      have haux : (1 / 16 : ℝ) ≤ S.U / w.u := by
        apply (le_div_iff₀ hu).2
        nlinarith
      exact haux.trans hτlo'
    have hτhi' : w.tau z ≤ (16 * S.U) / w.u := by
      apply (le_div_iff₀ hu).2
      simpa [mul_comm] using hz.2.1
    have hτhi : w.tau z ≤ 16 := by
      calc
        w.tau z ≤ (16 * S.U) / w.u := hτhi'
        _ ≤ 16 := by
          apply (div_le_iff₀ hu).2
          nlinarith
    have hτpos : 0 < w.tau z := by linarith
    have hvtau : 0 ≤ w.v * w.tau z := (mul_nonneg hv.le hτpos.le)
    have hvtauU : w.v * w.tau z ≤ 32 * S.V := by
      calc
        w.v * w.tau z ≤ w.v * 16 := mul_le_mul_of_nonneg_left hτhi hv.le
        _ ≤ (2 * S.V) * 16 := mul_le_mul_of_nonneg_right hvR (by norm_num)
        _ = 32 * S.V := by ring
    have hz2lo' : -31 * S.V ≤ (z.2 : ℝ) / w.u := by
      have h := hz.2.2.1
      linarith
    have hz2hi' : (z.2 : ℝ) / w.u ≤ 2 * S.V := by
      have h := hz.2.2.2
      linarith
    have hz2lo : (-31 * S.V) * w.u ≤ (z.2 : ℝ) :=
      (le_div_iff₀ hu).mp hz2lo'
    have hz2hi : (z.2 : ℝ) ≤ (2 * S.V) * w.u :=
      (div_le_iff₀ hu).mp hz2hi'
    have hz2loB : -(496 * S.U * S.V) ≤ (z.2 : ℝ) := by
      calc
        -(496 * S.U * S.V) = (-31 * S.V) * (16 * S.U) := by ring
        _ ≤ (-31 * S.V) * w.u :=
          mul_le_mul_of_nonpos_left huR (by nlinarith [hV])
        _ ≤ (z.2 : ℝ) := hz2lo
    have hz2hiB : (z.2 : ℝ) ≤ 32 * S.U * S.V := by
      calc
        (z.2 : ℝ) ≤ (2 * S.V) * w.u := hz2hi
        _ ≤ (2 * S.V) * (16 * S.U) :=
          mul_le_mul_of_nonneg_left huR (by positivity)
        _ = 32 * S.U * S.V := by ring
    have hz2Real : |(z.2 : ℝ)| ≤ M := by
      rw [abs_le]
      constructor
      · dsimp [M]
        linarith [hz2loB, hUV]
      · dsimp [M]
        linarith [hz2hiB, hUV]
    have hrzlo : -(496 * S.U * S.V) ≤ w.r * (z.2 : ℝ) := by
      by_cases hz20 : 0 ≤ (z.2 : ℝ)
      · have h := mul_nonneg hrL hz20
        linarith [hUV]
      · have hrle : w.r - 1 ≤ 0 := by linarith [hrU]
        have hz2le : (z.2 : ℝ) ≤ 0 := le_of_lt (lt_of_not_ge hz20)
        have h := mul_nonneg_of_nonpos_of_nonpos hrle hz2le
        linarith [hz2loB]
    have hrzhi : w.r * (z.2 : ℝ) ≤ 496 * S.U * S.V := by
      by_cases hz20 : 0 ≤ (z.2 : ℝ)
      · have hrOne : 0 ≤ 1 - w.r := by linarith [hrU]
        have h := mul_nonneg hrOne hz20
        nlinarith [hz2hiB]
      · have h := mul_nonpos_of_nonneg_of_nonpos hrL (le_of_lt (lt_of_not_ge hz20))
        nlinarith [hUV]
    have hz1lo : -(496 * S.U * S.V) ≤ (z.1 : ℝ) := by
      have ht : w.tau z = (z.1 : ℝ) + w.r * (z.2 : ℝ) := rfl
      linarith [ht, hτlo, hrzhi]
    have hz1hi : (z.1 : ℝ) ≤ 16 + 496 * S.U * S.V := by
      have ht : w.tau z = (z.1 : ℝ) + w.r * (z.2 : ℝ) := rfl
      linarith [ht, hτhi, hrzlo]
    have hz1Real : |(z.1 : ℝ)| ≤ M := by
      rw [abs_le]
      constructor <;> dsimp [M] <;> linarith [hz1lo, hz1hi, hUV]
    have hn1loR : -(n : ℝ) ≤ (z.1 : ℝ) :=
      (by linarith [hn] : -(n : ℝ) ≤ -M).trans (abs_le.mp hz1Real).1
    have hn1hiR : (z.1 : ℝ) ≤ (n : ℝ) := (abs_le.mp hz1Real).2.trans hn
    have hn2loR : -(n : ℝ) ≤ (z.2 : ℝ) :=
      (by linarith [hn] : -(n : ℝ) ≤ -M).trans (abs_le.mp hz2Real).1
    have hn2hiR : (z.2 : ℝ) ≤ (n : ℝ) := (abs_le.mp hz2Real).2.trans hn
    have hn1lo : -(n : ℤ) ≤ z.1 := by exact_mod_cast hn1loR
    have hn1hi : z.1 ≤ (n : ℤ) := by exact_mod_cast hn1hiR
    have hn2lo : -(n : ℤ) ≤ z.2 := by exact_mod_cast hn2loR
    have hn2hi : z.2 ≤ (n : ℤ) := by exact_mod_cast hn2hiR
    constructor
    · simpa [I, Set.mem_Icc] using ⟨hn1lo, hn1hi⟩
    · simpa [I, Set.mem_Icc] using ⟨hn2lo, hn2hi⟩
  have hZ : Z.Finite := (Set.finite_Icc _ _).prod (Set.finite_Icc _ _) |>.subset hZsub
  let P : Finset (PrimeLists S.x K) :=
    Fintype.piFinset fun i : Fin K =>
      Fintype.piFinset fun j : Fin (slotCount S.x) => primeBand S.x (F.a i)
  have hP (p : PrimeLists S.x K)
      (hp : ∀ i j, p i j ∈ primeBand S.x (F.a i)) : p ∈ P := by
    simp only [P, Fintype.mem_piFinset]
    intro i j
    exact hp i j
  have hset :
      {s : EnvPoint S.x K | (∀ i j, s.2 i j ∈ primeBand S.x (F.a i)) ∧
        envBox S w s.1} ⊆ Z ×ˢ (P : Set (PrimeLists S.x K)) := by
    intro s hs
    exact ⟨hs.2, Finset.mem_coe.mpr (hP s.2 hs.1)⟩
  exact (hZ.prod P.finite_toSet).subset hset

private theorem envPoint_valid_box_finite {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (hU : 0 < S.U) (hV : 0 < S.V) (hw : w.InRegion S) :
    {s : EnvPoint S.x K | EnvValid F S s ∧ envBox S w s.1}.Finite := by
  apply (envPoint_band_box_finite F S w hU hV hw).subset
  intro s hs
  exact ⟨fun i j => (hs.1.2.1 i j).2, hs.2⟩

private def historyDefaultPoint {x : ℝ} {K : ℕ} : EnvPoint x K :=
  ((0, 0), fun _ _ => 0)

private def historyDefaultPath {x : ℝ} {K : ℕ} : EnvPath x K :=
  fun _ => historyDefaultPoint

private def historyRouteIndex {x : ℝ} (k : ℕ) : Fin (pathLength x + 1) :=
  ⟨pathLength x - k, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩

private noncomputable def historyRouteFinset {x : ℝ} {K : ℕ}
    (P : Finset (EnvPoint x K)) (k : ℕ) : Finset (EnvPath x K) :=
  Fintype.piFinset fun j : Fin (pathLength x + 1) =>
    if pathLength x - k ≤ j.val then P else {historyDefaultPoint}

private theorem mem_historyRouteFinset {x : ℝ} {K : ℕ}
    (P : Finset (EnvPoint x K)) (k : ℕ) (γ : EnvPath x K) :
    γ ∈ historyRouteFinset P k ↔
      (∀ j, pathLength x - k ≤ j.val → γ j ∈ P) ∧
      (∀ j, j.val < pathLength x - k → γ j = historyDefaultPoint) := by
  simp only [historyRouteFinset, Fintype.mem_piFinset]
  constructor
  · intro h
    constructor
    · intro j hj
      simpa [hj] using h j
    · intro j hj
      have hnot : ¬ pathLength x - k ≤ j.val := by omega
      simpa [hnot] using h j
  · rintro ⟨hP, hD⟩ j
    by_cases hj : pathLength x - k ≤ j.val
    · simpa [hj] using hP j hj
    · simpa [hj] using hD j (by omega)

private theorem historyRouteFinset_zero_sum {x : ℝ} {K : ℕ}
    (P : Finset (EnvPoint x K)) (f : EnvPath x K → ℂ) :
    (∑ γ ∈ historyRouteFinset P 0, f γ) =
      ∑ e ∈ P, f (Function.update historyDefaultPath (Fin.last (pathLength x)) e) := by
  classical
  refine Finset.sum_bij
    (fun γ _ => γ (Fin.last (pathLength x)))
    ?_ ?_ ?_ ?_
  · intro γ hγ
    exact (mem_historyRouteFinset P 0 γ).mp hγ |>.1 _ (by simp)
  · intro γ₁ h₁ γ₂ h₂ he
    have h₁' := (mem_historyRouteFinset P 0 γ₁).mp h₁
    have h₂' := (mem_historyRouteFinset P 0 γ₂).mp h₂
    funext j
    by_cases hj : j = Fin.last (pathLength x)
    · simpa [hj] using he
    · have hjlt : j.val < pathLength x := by
        have hle : j.val ≤ pathLength x := by omega
        have hne : j.val ≠ pathLength x := by
          intro hval
          apply hj
          exact Fin.ext hval
        omega
      rw [h₁'.2 j hjlt, h₂'.2 j hjlt]
  · intro e he
    let γ := Function.update historyDefaultPath (Fin.last (pathLength x)) e
    refine ⟨γ, ?_, ?_⟩
    · rw [mem_historyRouteFinset]
      constructor
      · intro j hj
        have hjlast : j = Fin.last (pathLength x) := by
          apply Fin.ext
          simp only [Fin.val_last]
          omega
        subst j
        simpa [γ] using he
      · intro j hj
        have hjne : j ≠ Fin.last (pathLength x) := by
          intro h
          have := congrArg Fin.val h
          simp only [Fin.val_last] at this
          omega
        simp [γ, historyDefaultPath, Function.update_of_ne hjne]
    · simp [γ]
  · intro γ hγ
    have hγ' := (mem_historyRouteFinset P 0 γ).mp hγ
    have hEq : γ = Function.update historyDefaultPath (Fin.last (pathLength x))
        (γ (Fin.last (pathLength x))) := by
      funext j
      by_cases hj : j = Fin.last (pathLength x)
      · subst j
        simp
      · have hjlt : j.val < pathLength x := by
          have hle : j.val ≤ pathLength x := by omega
          have hne : j.val ≠ pathLength x := by
            intro heq
            apply hj
            exact Fin.ext heq
          omega
        have hdef := hγ'.2 j hjlt
        simp [historyDefaultPath, Function.update_of_ne hj, hdef]
    exact congrArg f hEq

private theorem historyRouteFinset_succ_sum {x : ℝ} {K : ℕ}
    (P : Finset (EnvPoint x K)) (k : ℕ) (hk : k < pathLength x)
    (f : EnvPath x K → ℂ) :
    (∑ γ ∈ historyRouteFinset P (k + 1), f γ) =
      ∑ e ∈ P, ∑ γ ∈ historyRouteFinset P k,
        f (Function.update γ (historyRouteIndex (k + 1)) e) := by
  classical
  let idx := historyRouteIndex (x := x) (k + 1)
  have hidxval : idx.val = pathLength x - (k + 1) := rfl
  have hidxlt : idx.val < pathLength x - k := by
    dsimp [idx, historyRouteIndex]
    omega
  rw [← Finset.sum_product']
  refine Finset.sum_bij
    (fun γ _ => (γ idx, Function.update γ idx historyDefaultPoint))
    ?_ ?_ ?_ ?_
  · intro γ hγ
    have hγ' := (mem_historyRouteFinset P (k + 1) γ).mp hγ
    apply Finset.mem_product.mpr
    constructor
    · exact hγ'.1 idx (by simp [idx, historyRouteIndex])
    · rw [mem_historyRouteFinset]
      constructor
      · intro j hj
        by_cases hji : j = idx
        · subst j
          exact False.elim (not_le_of_gt hidxlt hj)
        · have hj' : pathLength x - (k + 1) ≤ j.val := by
            dsimp [idx, historyRouteIndex] at hji
            omega
          have hmem := hγ'.1 j hj'
          simpa [Function.update_of_ne hji] using hmem
      · intro j hj
        by_cases hji : j = idx
        · subst j
          simp [idx, historyRouteIndex]
        · have hj' : j.val < pathLength x - (k + 1) := by
            have hjiVal : j.val ≠ idx.val := by
              intro heq
              apply hji
              exact Fin.ext heq
            omega
          have hdef := hγ'.2 j hj'
          simpa [Function.update_of_ne hji] using hdef
  · intro γ₁ h₁ γ₂ h₂ heq
    have he : γ₁ idx = γ₂ idx := congrArg Prod.fst heq
    have hrest : Function.update γ₁ idx historyDefaultPoint =
        Function.update γ₂ idx historyDefaultPoint := congrArg Prod.snd heq
    funext j
    by_cases hji : j = idx
    · simpa [hji] using he
    · have h := congrFun hrest j
      simpa [Function.update_of_ne hji] using h
  · intro pair hp
    rcases Finset.mem_product.mp hp with ⟨he, hγ⟩
    let γ := Function.update pair.2 idx pair.1
    refine ⟨γ, ?_, ?_⟩
    · rw [mem_historyRouteFinset]
      constructor
      · intro j hj
        by_cases hji : j = idx
        · subst j
          simpa [γ, idx] using he
        · have hj' : pathLength x - k ≤ j.val := by
            have hjiVal : j.val ≠ idx.val := by
              intro heq
              apply hji
              exact Fin.ext heq
            omega
          have hγprop := (mem_historyRouteFinset P k pair.2).mp hγ
          have hmem := hγprop.1 j hj'
          simpa [γ, Function.update_of_ne hji] using hmem
      · intro j hj
        by_cases hji : j = idx
        · subst j
          have : ¬ idx.val < pathLength x - (k + 1) := by omega
          exact False.elim (this hj)
        · have hj' : j.val < pathLength x - k := by
            dsimp [idx, historyRouteIndex] at hji
            omega
          have hγprop := (mem_historyRouteFinset P k pair.2).mp hγ
          have hdef := hγprop.2 j hj'
          simpa [γ, Function.update_of_ne hji] using hdef
    · apply Prod.ext
      · simp [γ]
      · have hγprop := (mem_historyRouteFinset P k pair.2).mp hγ
        have hdefault : pair.2 idx = historyDefaultPoint := hγprop.2 idx hidxlt
        funext j
        by_cases hji : j = idx
        · subst j
          simp [γ, hdefault]
        · simp [γ, Function.update_of_ne hji]
  · intro γ hγ
    have hγ' := (mem_historyRouteFinset P (k + 1) γ).mp hγ
    have hreconstruct : γ = Function.update
        (Function.update γ idx historyDefaultPoint) idx (γ idx) := by
      funext j
      by_cases hji : j = idx <;> simp [hji]
    exact congrArg f hreconstruct

private theorem validPrimeLists_permute {x : ℝ} {K : ℕ} {a : Fin K → ℝ}
    (σ : Fin K → Equiv.Perm (Fin (slotCount x))) (p : PrimeLists x K)
    (hp : ValidPrimeLists x K a p) : ValidPrimeLists x K a (permuteLists σ p) := by
  constructor
  · intro i j
    exact hp.1 i (σ i j)
  · intro i j j' hj
    apply hp.2 i (σ i j) (σ i j')
    intro h
    exact hj ((σ i).injective h)

private theorem edgeAdmissible_target_valid_box {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) {s : MemPoint S.x K}
    {c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i} {z' : ℤ × ℤ}
    (h : EdgeAdmissible F S w s c z') :
    EnvValid F S (z', edgeTargetLists F S s c) ∧ envBox S w z' := by
  rcases h with ⟨_, _, hLists, _, _, hGcd, _, hBox, _, _⟩
  exact ⟨⟨hGcd, hLists⟩, hBox⟩

private theorem tsum_sum_finite_support {α ι : Type*} (T : Finset α) (s : Finset ι)
    (f : α → ι → ℂ) (hzero : ∀ i a, a ∉ T → f a i = 0) :
    (∑' a, ∑ i ∈ s, f a i) = ∑ i ∈ s, ∑' a, f a i := by
  calc
    _ = ∑ a ∈ T, ∑ i ∈ s, f a i := by
      apply tsum_eq_sum
      intro a ha
      simp [hzero _ _ ha]
    _ = ∑ i ∈ s, ∑ a ∈ T, f a i := by rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      symm
      apply tsum_eq_sum
      intro a ha
      exact hzero i a ha

private theorem edgeAdmissible_position_mem {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) {s : MemPoint S.x K}
    {c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i} {z' : ℤ × ℤ}
    {P : Finset (EnvPoint S.x K)}
    (hP : ∀ t, t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1)
    (h : EdgeAdmissible F S w s c z') : z' ∈ P.image fun t => t.1 := by
  apply Finset.mem_image.mpr
  refine ⟨(z', edgeTargetLists F S s c), ?_, rfl⟩
  exact hP _ |>.2 (edgeAdmissible_target_valid_box F S w h)

private theorem logEdgePiece_sum {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (w : ArchRoot) (step : ℕ) (raw : Bool) (St Pr : Finset (Fin K))
    {ι : Type*} (R : Finset ι) (f : ι → LogPoint S.x K → ℂ)
    (P : Finset (EnvPoint S.x K))
    (hP : ∀ t, t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1)
    (σL : LogPoint S.x K) :
    logEdgePiece F S ρ w step raw St Pr (fun t => ∑ i ∈ R, f i t) σL =
      ∑ i ∈ R, logEdgePiece F S ρ w step raw St Pr (f i) σL := by
  classical
  let s := σL.1
  let good (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ) : Prop :=
    edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧ EdgeAdmissible F S w s c z'
  let out (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ) :
      LogPoint S.x K :=
    ((z', (edgeTargetLists F S s c, edgeNewMemory F S s c)),
      σL.2 ++ edgeBirths F S step s c)
  let coef (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ) : ℂ :=
    (((ρ ^ (∑ i : Fin K, hitCount (s.2.2 i) s.1) *
        (∏ i : Fin K,
          match (c i).2 with
          | Sum.inl _ => (bandMass S.x (F.a i))⁻¹
          | Sum.inr p => memoryNu S.x K F.a F.q_d i p) *
        ρ ^ (∑ i : Fin K, hitCount (edgeNewMemory F S s c i) z') : ℝ) : ℂ) *
      edgeMultiplier F S (decide (step % 2 = 0)) raw s.2.1
        (edgeTargetLists F S s c) s.1 z')
  change
    (∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
      ∑' z' : ℤ × ℤ,
        if good c z' then coef c z' * (∑ i ∈ R, f i (out c z')) else 0) =
      ∑ i ∈ R,
        (∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
          ∑' z' : ℤ × ℤ,
            if good c z' then coef c z' * f i (out c z') else 0)
  have hpoint (c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i) (z' : ℤ × ℤ) :
      (if good c z' then coef c z' * (∑ i ∈ R, f i (out c z')) else 0) =
        ∑ i ∈ R, if good c z' then coef c z' * f i (out c z') else 0 := by
    by_cases hg : good c z' <;> simp [hg, Finset.mul_sum]
  simp_rw [hpoint]
  calc
    _ = ∑ c : (i : Fin K) → EdgeChoice S.x F.a (s.2.2 i) i,
          ∑ i ∈ R, ∑' z' : ℤ × ℤ,
            if good c z' then coef c z' * f i (out c z') else 0 := by
          apply Finset.sum_congr rfl
          intro c hc
          apply tsum_sum_finite_support (P.image fun t => t.1) R
          intro i z' hz'
          by_cases hg : good c z'
          · have hzmem := edgeAdmissible_position_mem F S w hP hg.2.2
            exact (hz' hzmem).elim
          · simp [hg]
    _ = _ := by rw [Finset.sum_comm]

private theorem logSym_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    {ι : Type*} (R : Finset ι) (f : ι → LogPoint S.x K → ℂ) :
    logSym F S (fun t => ∑ i ∈ R, f i t) =
      fun t => ∑ i ∈ R, logSym F S (f i) t := by
  classical
  funext σL
  unfold logSym
  calc
    ((permCount S.x K : ℂ))⁻¹ *
        ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          ∑ i ∈ R, f i ((σL.1.1, permuteLists σ σL.1.2.1, σL.1.2.2), σL.2) =
      ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
        ∑ i ∈ R, ((permCount S.x K : ℂ))⁻¹ *
          f i ((σL.1.1, permuteLists σ σL.1.2.1, σL.1.2.2), σL.2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro σ hσ
            rw [Finset.mul_sum]
    _ = ∑ i ∈ R, ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
          ((permCount S.x K : ℂ))⁻¹ *
            f i ((σL.1.1, permuteLists σ σL.1.2.1, σL.1.2.2), σL.2) := by
          rw [Finset.sum_comm]
    _ = ∑ i ∈ R, ((permCount S.x K : ℂ))⁻¹ *
          ∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
            f i ((σL.1.1, permuteLists σ σL.1.2.1, σL.1.2.2), σL.2) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    _ = ∑ i ∈ R, logSym F S (f i) σL := rfl

private theorem logEdge_full_sum {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ)
    (w : ArchRoot) (step : ℕ) {ι : Type*} (R : Finset ι)
    (f : ι → LogPoint S.x K → ℂ) (P : Finset (EnvPoint S.x K))
    (hP : ∀ t, t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1) :
    logEdge F S ρ w EdgeKind.full step (fun t => ∑ i ∈ R, f i t) =
      fun t => ∑ i ∈ R, logEdge F S ρ w EdgeKind.full step (f i) t := by
  classical
  have hPiece (raw : Bool) (St Pr : Finset (Fin K)) (σL : LogPoint S.x K) :
      logEdgePiece F S ρ w step raw St Pr
          (logSym F S (fun t => ∑ i ∈ R, f i t)) σL =
        ∑ i ∈ R, logEdgePiece F S ρ w step raw St Pr (logSym F S (f i)) σL := by
    rw [logSym_sum]
    exact logEdgePiece_sum F S ρ w step raw St Pr R
      (fun i => logSym F S (f i)) P hP σL
  have hInner :
      (fun σL => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr
            (logSym F S (fun t => ∑ i ∈ R, f i t)) σL -
          logEdgePiece F S ρ w step false St Pr
            (logSym F S (fun t => ∑ i ∈ R, f i t)) σL)) =
      (fun σL => ∑ i ∈ R, ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr (logSym F S (f i)) σL -
          logEdgePiece F S ρ w step false St Pr (logSym F S (f i)) σL)) := by
    funext σL
    simp_rw [hPiece]
    simp_rw [← Finset.sum_sub_distrib]
    calc
      ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K), ∑ i ∈ R,
          (logEdgePiece F S ρ w step true St Pr (logSym F S (f i)) σL -
            logEdgePiece F S ρ w step false St Pr (logSym F S (f i)) σL) =
        ∑ St : Finset (Fin K), ∑ i ∈ R, ∑ Pr : Finset (Fin K),
          (logEdgePiece F S ρ w step true St Pr (logSym F S (f i)) σL -
            logEdgePiece F S ρ w step false St Pr (logSym F S (f i)) σL) := by
              apply Finset.sum_congr rfl
              intro St hSt
              rw [Finset.sum_comm]
      _ = ∑ i ∈ R, ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
          (logEdgePiece F S ρ w step true St Pr (logSym F S (f i)) σL -
            logEdgePiece F S ρ w step false St Pr (logSym F S (f i)) σL) := by
              rw [Finset.sum_comm]
  funext σL
  change logSym F S
      (fun t => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr
            (logSym F S (fun u => ∑ i ∈ R, f i u)) t -
          logEdgePiece F S ρ w step false St Pr
            (logSym F S (fun u => ∑ i ∈ R, f i u)) t)) σL = _
  rw [hInner, logSym_sum]
  rfl

private theorem envPoint_permute_mem {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (P : Finset (EnvPoint S.x K))
    (hP : ∀ t, t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1)
    (σ : Fin K → Equiv.Perm (Fin (slotCount S.x))) (t : EnvPoint S.x K)
    (ht : t ∈ P) : (t.1, permuteLists σ t.2) ∈ P := by
  apply (hP (t.1, permuteLists σ t.2)).mpr
  have h := (hP t).mp ht
  refine ⟨⟨h.1.1, validPrimeLists_permute σ t.2 h.1.2⟩, ?_⟩
  exact h.2

private theorem logSym_congr_on_P {K : ℕ} (F : PDFix K) (S : PDScale)
    (w : ArchRoot) (P : Finset (EnvPoint S.x K))
    (hP : ∀ t, t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1)
    (f g : LogPoint S.x K → ℂ)
    (hfg : ∀ σL, (σL.1.1, σL.1.2.1) ∈ P → f σL = g σL)
    (σL : LogPoint S.x K) (hσ : (σL.1.1, σL.1.2.1) ∈ P) :
    logSym F S f σL = logSym F S g σL := by
  classical
  unfold logSym
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ'
  apply hfg
  exact envPoint_permute_mem F S w P hP σ (σL.1.1, σL.1.2.1) hσ

private theorem logEdgePiece_congr_on_P {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ) (raw : Bool) (St Pr : Finset (Fin K))
    (P : Finset (EnvPoint S.x K))
    (hP : ∀ t, t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1)
    (f g : LogPoint S.x K → ℂ)
    (hfg : ∀ σL, (σL.1.1, σL.1.2.1) ∈ P → f σL = g σL)
    (σL : LogPoint S.x K) :
    logEdgePiece F S ρ w step raw St Pr f σL =
      logEdgePiece F S ρ w step raw St Pr g σL := by
  classical
  let out (c : (i : Fin K) → EdgeChoice S.x F.a (σL.1.2.2 i) i) (z' : ℤ × ℤ) :
      LogPoint S.x K :=
    ((z', (edgeTargetLists F S σL.1 c, edgeNewMemory F S σL.1 c)),
      σL.2 ++ edgeBirths F S step σL.1 c)
  unfold logEdgePiece
  apply Finset.sum_congr rfl
  intro c hc
  apply tsum_congr
  intro z'
  by_cases hg : edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
      EdgeAdmissible F S w σL.1 c z'
  · simp only [if_pos hg]
    have hout : ((out c z').1.1, (out c z').1.2.1) ∈ P := by
      have htarget := (hP (z', edgeTargetLists F S σL.1 c)).mpr
        (edgeAdmissible_target_valid_box F S w hg.2.2)
      simpa [out] using htarget
    rw [hfg (out c z') hout]
  · simp [hg]

private theorem logEdge_full_congr_on_P {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ) (P : Finset (EnvPoint S.x K))
    (hP : ∀ t, t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1)
    (f g : LogPoint S.x K → ℂ)
    (hfg : ∀ σL, (σL.1.1, σL.1.2.1) ∈ P → f σL = g σL)
    (σL : LogPoint S.x K) (hσ : (σL.1.1, σL.1.2.1) ∈ P) :
    logEdge F S ρ w EdgeKind.full step f σL =
      logEdge F S ρ w EdgeKind.full step g σL := by
  classical
  have hSym : ∀ τ, (τ.1.1, τ.1.2.1) ∈ P →
      logSym F S f τ = logSym F S g τ := by
    intro τ hτ
    exact logSym_congr_on_P F S w P hP f g hfg τ hτ
  have hInside :
      (fun τ => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr (logSym F S f) τ -
          logEdgePiece F S ρ w step false St Pr (logSym F S f) τ)) =
      (fun τ => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr (logSym F S g) τ -
          logEdgePiece F S ρ w step false St Pr (logSym F S g) τ)) := by
    funext τ
    apply Finset.sum_congr rfl
    intro St hSt
    apply Finset.sum_congr rfl
    intro Pr hPr
    rw [logEdgePiece_congr_on_P F S ρ w step true St Pr P hP _ _ hSym τ,
      logEdgePiece_congr_on_P F S ρ w step false St Pr P hP _ _ hSym τ]
  change logSym F S (fun τ => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr (logSym F S f) τ -
          logEdgePiece F S ρ w step false St Pr (logSym F S f) τ)) σL =
      logSym F S (fun τ => ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr (logSym F S g) τ -
          logEdgePiece F S ρ w step false St Pr (logSym F S g) τ)) σL
  exact congrArg (fun H : LogPoint S.x K → ℂ => logSym F S H σL) hInside

private theorem logSym_zero_of_badLog {K : ℕ} (F : PDFix K) (S : PDScale)
    (f : LogPoint S.x K → ℂ)
    (hf : ∀ σL, ¬ (σL.2.map Prod.snd).Nodup → f σL = 0)
    (σL : LogPoint S.x K) (hbad : ¬ (σL.2.map Prod.snd).Nodup) :
    logSym F S f σL = 0 := by
  classical
  unfold logSym
  have hsum :
      (∑ σ : Fin K → Equiv.Perm (Fin (slotCount S.x)),
        f ((σL.1.1, permuteLists σ σL.1.2.1, σL.1.2.2), σL.2)) = 0 := by
    apply Finset.sum_eq_zero
    intro σ hσ
    exact hf _ hbad
  simp [hsum]

private theorem bad_log_append_left {α : Type*} {l₁ l₂ : List α}
    (h : ¬ l₁.Nodup) : ¬ (l₁ ++ l₂).Nodup := by
  intro hn
  exact h (List.Nodup.of_append_left hn)

private theorem bad_log_append_right {α : Type*} {l₁ l₂ : List α}
    (h : ¬ l₂.Nodup) : ¬ (l₁ ++ l₂).Nodup := by
  intro hn
  exact h (List.Nodup.of_append_right hn)

private theorem tsum_zero_of_eq_zero {α : Type*} (f : α → ℂ)
    (h : ∀ a, f a = 0) : ∑' a, f a = 0 := by
  have hf : f = fun _ => 0 := funext h
  rw [hf]
  simp

private theorem logEdgePiece_zero_of_badLog {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ) (raw : Bool) (St Pr : Finset (Fin K))
    (f : LogPoint S.x K → ℂ)
    (hf : ∀ σL, ¬ (σL.2.map Prod.snd).Nodup → f σL = 0)
    (σL : LogPoint S.x K) (hbad : ¬ (σL.2.map Prod.snd).Nodup) :
    logEdgePiece F S ρ w step raw St Pr f σL = 0 := by
  classical
  unfold logEdgePiece
  apply Finset.sum_eq_zero
  intro c hc
  apply tsum_zero_of_eq_zero
  intro z'
  by_cases hg : edgeStoredSet c = St ∧ edgePromotedSet c = Pr ∧
      EdgeAdmissible F S w σL.1 c z'
  · have hbadOut :
        ¬ ((σL.2 ++ edgeBirths F S step σL.1 c).map Prod.snd).Nodup := by
      simpa [List.map_append] using
        (bad_log_append_left hbad :
          ¬ (σL.2.map Prod.snd ++ (edgeBirths F S step σL.1 c).map Prod.snd).Nodup)
    let out : LogPoint S.x K :=
      ((z', (edgeTargetLists F S σL.1 c, edgeNewMemory F S σL.1 c)),
        σL.2 ++ edgeBirths F S step σL.1 c)
    have hfout : f out = 0 := hf out (by simpa [out] using hbadOut)
    simp [hg, out, hfout]
  · simp [hg]

private theorem logEdge_full_zero_of_badLog {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (step : ℕ)
    (f : LogPoint S.x K → ℂ)
    (hf : ∀ σL, ¬ (σL.2.map Prod.snd).Nodup → f σL = 0)
    (σL : LogPoint S.x K) (hbad : ¬ (σL.2.map Prod.snd).Nodup) :
    logEdge F S ρ w EdgeKind.full step f σL = 0 := by
  classical
  have hSym : ∀ τ, ¬ (τ.2.map Prod.snd).Nodup → logSym F S f τ = 0 :=
    fun τ hτ => logSym_zero_of_badLog F S f hf τ hτ
  have hInside : ∀ τ, ¬ (τ.2.map Prod.snd).Nodup →
      (∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
        (logEdgePiece F S ρ w step true St Pr (logSym F S f) τ -
          logEdgePiece F S ρ w step false St Pr (logSym F S f) τ)) = 0 := by
    intro τ hτ
    apply Finset.sum_eq_zero
    intro St hSt
    apply Finset.sum_eq_zero
    intro Pr hPr
    rw [logEdgePiece_zero_of_badLog F S ρ w step true St Pr (logSym F S f)
          hSym τ hτ,
        logEdgePiece_zero_of_badLog F S ρ w step false St Pr (logSym F S f)
          hSym τ hτ]
    ring
  unfold logEdge
  simp only [EdgeKind.full]
  apply logSym_zero_of_badLog F S (fun τ =>
    ∑ St : Finset (Fin K), ∑ Pr : Finset (Fin K),
      (logEdgePiece F S ρ w step true St Pr (logSym F S f) τ -
        logEdgePiece F S ρ w step false St Pr (logSym F S f) τ)) hInside σL hbad

private theorem logGhost_zero_of_badLog {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) (f : LogPoint S.x K → ℂ)
    (hf : ∀ σL, ¬ (σL.2.map Prod.snd).Nodup → f σL = 0)
    (σL : LogPoint S.x K) (hbad : ¬ (σL.2.map Prod.snd).Nodup) :
    logGhost F S ρ j f σL = 0 := by
  classical
  unfold logGhost
  apply Finset.sum_eq_zero
  intro D hD
  apply tsum_zero_of_eq_zero
  intro l
  apply Finset.sum_eq_zero
  intro new hnew
  by_cases hDsub : ∀ i, D i ⊆ hitIndices (σL.1.2.2 i) σL.1.1
  · let batch : BirthLog K := (List.finRange K).flatMap (fun i =>
      List.ofFn fun k : Fin (l i) =>
        (BirthAddress.ghost j i k.val, ((new i k : ℕ))))
    have hbadAppend : ¬ (σL.2.map Prod.snd ++ batch.map Prod.snd).Nodup :=
      bad_log_append_left hbad
    have hbadOut : ¬ ((σL.2 ++ batch).map Prod.snd).Nodup := by
      simpa [List.map_append] using hbadAppend
    let out : LogPoint S.x K :=
      ((σL.1.1, σL.1.2.1, fun i =>
          removeIndices (σL.1.2.2 i) (D i) ++
            List.ofFn fun k : Fin (l i) => anchorAt (new i k) σL.1.1),
        σL.2 ++ batch)
    have hfout : f out = 0 := hf out (by simpa [out] using hbadOut)
    simp only [if_pos hDsub]
    change (((∏ i : Fin K, ghostGroupCoeff F S ρ j i
        (hitCount (σL.1.2.2 i) σL.1.1) (D i).card (l i)
        (List.ofFn fun k => (new i k : ℕ)) : ℝ) : ℂ) * f out) = 0
    rw [hfout]
    simp
  · simp [hDsub]

private theorem logHistoryFn_zero_of_badLog {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (γ : Option (EnvPath S.x K)) :
    ∀ k σL, ¬ (σL.2.map Prod.snd).Nodup →
      logHistoryFn F S ρ w none γ distinctWeight k σL = 0 := by
  intro k
  induction k with
  | zero =>
      intro σL hbad
      have hboundary : ∀ τ : LogPoint S.x K, ¬ (τ.2.map Prod.snd).Nodup →
          logBoundaryOut distinctWeight τ = 0 := by
        intro τ hτ
        simp [logBoundaryOut, distinctWeight, hτ]
      have hghost := logGhost_zero_of_badLog F S ρ (pathLength S.x)
        (logBoundaryOut distinctWeight) hboundary σL hbad
      have hghostTrunc :
          logGhost F S ρ (pathLength S.x)
            (logTrunc none (logBoundaryOut distinctWeight)) σL = 0 := by
        change logGhost F S ρ (pathLength S.x) (logBoundaryOut distinctWeight) σL = 0
        exact hghost
      cases γ with
      | none => simpa [logHistoryFn, logTrunc, logPathRestrict] using hghostTrunc
      | some path => simp [logHistoryFn, logTrunc, logPathRestrict, hghostTrunc]
  | succ k ih =>
      intro σL hbad
      have hEdge : ∀ τ, ¬ (τ.2.map Prod.snd).Nodup →
          logEdge F S ρ w EdgeKind.full (pathLength S.x - (k + 1))
            (logHistoryFn F S ρ w none γ distinctWeight k) τ = 0 := by
        intro τ hτ
        exact logEdge_full_zero_of_badLog F S ρ w (pathLength S.x - (k + 1))
          (logHistoryFn F S ρ w none γ distinctWeight k) (fun σ hσ => ih σ hσ) τ hτ
      have hghost := logGhost_zero_of_badLog F S ρ (pathLength S.x - (k + 1))
        (logEdge F S ρ w EdgeKind.full (pathLength S.x - (k + 1))
          (logHistoryFn F S ρ w none γ distinctWeight k)) hEdge σL hbad
      have hghostTrunc :
          logGhost F S ρ (pathLength S.x - (k + 1))
            (logTrunc none
              (logEdge F S ρ w EdgeKind.full (pathLength S.x - (k + 1))
                (logTrunc none (logHistoryFn F S ρ w none γ distinctWeight k)))) σL = 0 := by
        change logGhost F S ρ (pathLength S.x - (k + 1))
          (logEdge F S ρ w EdgeKind.full (pathLength S.x - (k + 1))
            (logHistoryFn F S ρ w none γ distinctWeight k)) σL = 0
        exact hghost
      cases γ with
      | none => simpa [logHistoryFn, logTrunc, logPathRestrict] using hghostTrunc
      | some path => simp [logHistoryFn, logTrunc, logPathRestrict, hghostTrunc]

/-- A repeated prime in a birth log is annihilated by the terminal distinctness weight,
including after every untruncated history operator. -/
theorem pd_life_b_logHistoryFn_zero_of_badLog {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (γ : Option (EnvPath S.x K)) (k : ℕ)
    (σL : LogPoint S.x K) (hbad : ¬ (σL.2.map Prod.snd).Nodup) :
    logHistoryFn F S ρ w none γ distinctWeight k σL = 0 :=
  logHistoryFn_zero_of_badLog F S ρ w γ k σL hbad

private theorem logHistoryFn_congrPath {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (W : BirthLog K → ℂ) (k : ℕ)
    (γ γ' : EnvPath S.x K)
    (hγ : ∀ j, pathLength S.x - k ≤ j.val → γ j = γ' j) :
    logHistoryFn F S ρ w none (some γ) W k =
      logHistoryFn F S ρ w none (some γ') W k := by
  induction k with
  | zero =>
      have hlast : γ (Fin.last (pathLength S.x)) = γ' (Fin.last (pathLength S.x)) :=
        hγ _ (by simp)
      have hlast' : γ ⟨pathLength S.x, Nat.lt_succ_self _⟩ =
          γ' ⟨pathLength S.x, Nat.lt_succ_self _⟩ := by
        simpa [Fin.last] using hlast
      funext σL
      simp [logHistoryFn, logTrunc, logPathRestrict, hlast']
  | succ k ih =>
      let idx := historyRouteIndex (x := S.x) (k + 1)
      have hcur : γ idx = γ' idx := hγ idx (by simp [idx, historyRouteIndex])
      have hcur' : γ ⟨pathLength S.x - (k + 1), by omega⟩ =
          γ' ⟨pathLength S.x - (k + 1), by omega⟩ := by
        simpa [idx, historyRouteIndex] using hcur
      have htail : ∀ j, pathLength S.x - k ≤ j.val → γ j = γ' j := by
        intro j hj
        exact hγ j (by omega)
      have hrec := ih htail
      funext σL
      simp only [logHistoryFn, logTrunc]
      rw [hrec]
      simp [logPathRestrict, hcur']

private def historyGhostBatchLog {K : ℕ} (F : PDFix K) (S : PDScale) (j : ℕ)
    (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)) : BirthLog K :=
  (List.finRange K).flatMap fun i =>
    List.ofFn fun k : Fin (l i) => (BirthAddress.ghost j i k.val, (new i k : ℕ))

private theorem historyListFinRangeSum {n : ℕ} (g : Fin n → ℕ) :
    ((List.finRange n).map g).sum = ∑ i : Fin n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ]
      simp only [List.map_cons, List.map_map, Function.comp_def, List.sum_cons,
        Fin.sum_univ_succ]
      simpa using congrArg (fun z => g 0 + z) (ih fun i => g i.succ)

private theorem historyGhostBatch_values_mem {K : ℕ} (F : PDFix K) (S : PDScale)
    (j : ℕ) (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i))
    {p : ℕ} (hp : p ∈ (historyGhostBatchLog F S j l new).map Prod.snd) :
    p ∈ markedPrimes S.x K F.a := by
  classical
  simp only [historyGhostBatchLog, List.map_flatMap, List.mem_flatMap, List.mem_map] at hp
  rcases hp with ⟨i, hi, b, hb, hbp⟩
  rcases List.mem_ofFn.mp hb with ⟨k, hk⟩
  have hval : (new i k : ℕ) = p := by
    calc
      (new i k : ℕ) = (BirthAddress.ghost j i k.val, (new i k : ℕ)).2 := rfl
      _ = b.2 := congrArg Prod.snd hk
      _ = p := hbp
  have hval' : p = (new i k : ℕ) := hval.symm
  rw [hval']
  apply Finset.mem_biUnion.mpr
  exact ⟨i, Finset.mem_univ i, (new i k).property⟩

private theorem historyGhostBatch_values_length {K : ℕ} (F : PDFix K) (S : PDScale)
    (j : ℕ) (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)) :
    ((historyGhostBatchLog F S j l new).map Prod.snd).length = ∑ i : Fin K, l i := by
  classical
  simp only [historyGhostBatchLog, List.length_map, List.length_flatMap, List.length_ofFn]
  exact historyListFinRangeSum l

private theorem historyGhostBatch_not_nodup {K : ℕ} (F : PDFix K) (S : PDScale)
    (j : ℕ) (l : Fin K → ℕ)
    (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i))
    (hl : (markedPrimes S.x K F.a).card < ∑ i : Fin K, l i) :
    ¬ ((historyGhostBatchLog F S j l new).map Prod.snd).Nodup := by
  intro hnd
  have hsubset :
      ((historyGhostBatchLog F S j l new).map Prod.snd).toFinset ⊆ markedPrimes S.x K F.a := by
    intro p hp
    exact historyGhostBatch_values_mem F S j l new (by simpa using hp)
  have hcard := List.toFinset_card_of_nodup hnd
  have hlen := historyGhostBatch_values_length F S j l new
  have hle :
      ((historyGhostBatchLog F S j l new).map Prod.snd).length ≤
        (markedPrimes S.x K F.a).card := by
    calc
      _ = ((historyGhostBatchLog F S j l new).map Prod.snd).toFinset.card := hcard.symm
      _ ≤ (markedPrimes S.x K F.a).card := Finset.card_mono hsubset
  omega

private theorem not_nodup_append_left {α : Type*} {l₁ l₂ : List α}
    (h : ¬ l₁.Nodup) : ¬ (l₁ ++ l₂).Nodup := by
  intro hn
  exact h (List.Nodup.of_append_left hn)

private theorem not_nodup_append_right {α : Type*} {l₁ l₂ : List α}
    (h : ¬ l₂.Nodup) : ¬ (l₁ ++ l₂).Nodup := by
  intro hn
  exact h (List.Nodup.of_append_right hn)

private theorem logGhost_sum_badLog {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) {ι : Type*} (R : Finset ι) (f : ι → LogPoint S.x K → ℂ)
    (hf : ∀ i σL, ¬ (σL.2.map Prod.snd).Nodup → f i σL = 0) :
    logGhost F S ρ j (fun σL => ∑ i ∈ R, f i σL) =
      fun σL => ∑ i ∈ R, logGhost F S ρ j (f i) σL := by
  classical
  funext σL
  let Q := (markedPrimes S.x K F.a).card
  let L : Finset (Fin K → ℕ) :=
    (Fintype.piFinset fun _ : Fin K => Finset.range (Q + 1)).filter
      (fun l => ∑ i : Fin K, l i ≤ Q)
  let good (D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length)) :=
    ∀ i, D i ⊆ hitIndices (σL.1.2.2 i) σL.1.1
  let out (D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length))
      (l : Fin K → ℕ) (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)) :
      LogPoint S.x K :=
    ((σL.1.1, σL.1.2.1, fun i => removeIndices (σL.1.2.2 i) (D i) ++
        List.ofFn fun k : Fin (l i) => anchorAt (new i k) σL.1.1),
      σL.2 ++ historyGhostBatchLog F S j l new)
  let coeff (D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length)
      ) (l : Fin K → ℕ) (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)) : ℂ :=
    ((∏ i : Fin K, ghostGroupCoeff F S ρ j i (hitCount (σL.1.2.2 i) σL.1.1)
        (D i).card (l i) (List.ofFn fun k => (new i k : ℕ)) : ℝ) : ℂ)
  let term (D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length)
      ) (l : Fin K → ℕ) (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i))
      (i : ι) : ℂ :=
    if good D then coeff D l new * f i (out D l new) else 0
  have hnotL (l : Fin K → ℕ) (hl : l ∉ L) :
      (markedPrimes S.x K F.a).card < ∑ i : Fin K, l i := by
    by_contra hn
    have hsum : ∑ i : Fin K, l i ≤ Q := by omega
    have hbound : ∀ i : Fin K, l i ≤ Q := by
      intro i
      have hle : l i ≤ ∑ j : Fin K, l j :=
        Finset.single_le_sum (s := Finset.univ) (f := l)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    have hpi : l ∈ Fintype.piFinset (fun _ : Fin K => Finset.range (Q + 1)) := by
      simp only [Fintype.mem_piFinset]
      intro i
      exact Finset.mem_range.mpr (by have := hbound i; omega)
    exact hl (Finset.mem_filter.mpr ⟨hpi, hsum⟩)
  have hbadTarget
      (D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length)
      ) (l : Fin K → ℕ)
      (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i))
      (hl : l ∉ L) : ¬ ((out D l new).2.map Prod.snd).Nodup := by
    have hbatch : ¬ ((historyGhostBatchLog F S j l new).map Prod.snd).Nodup :=
      historyGhostBatch_not_nodup F S j l new (by simpa [Q] using hnotL l hl)
    have happend :
        ¬ ((σL.2.map Prod.snd) ++ (historyGhostBatchLog F S j l new).map Prod.snd).Nodup :=
      bad_log_append_right hbatch
    simpa [out, List.map_append] using happend
  have hzero (D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length)
      ) (l : Fin K → ℕ) (hl : l ∉ L) (i : ι) :
      ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i), term D l new i = 0 := by
    apply Finset.sum_eq_zero
    intro new hnew
    by_cases hg : good D
    · simp only [term, if_pos hg]
      have hfout := hf i (out D l new) (hbadTarget D l new hl)
      simp [hfout]
    · simp [term, hg]
  have hterm (D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length)
      ) (l : Fin K → ℕ)
      (new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i)) :
      (if good D then coeff D l new * (∑ i ∈ R, f i (out D l new)) else 0) =
        ∑ i ∈ R, term D l new i := by
    by_cases hg : good D
    · simp [term, coeff, hg, Finset.mul_sum]
    · simp [term, hg]
  have hswapNew (D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length)
      ) (l : Fin K → ℕ) :
      (∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
        ∑ i ∈ R, term D l new i) =
      ∑ i ∈ R, ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
        term D l new i := by
    rw [Finset.sum_comm]
  have hswapL (D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length)) :
      (∑' l : Fin K → ℕ, ∑ i ∈ R,
        ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i), term D l new i) =
      ∑ i ∈ R, ∑' l : Fin K → ℕ,
        ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i), term D l new i :=
    tsum_sum_finite_support L R
      (fun l i => ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i), term D l new i)
      (by intro i l hl; exact hzero D l hl i)
  unfold logGhost
  change
    (∑ D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length),
      ∑' l : Fin K → ℕ, ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
        if good D then coeff D l new * (∑ i ∈ R, f i (out D l new)) else 0) =
    ∑ i ∈ R,
      ∑ D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length),
        ∑' l : Fin K → ℕ, ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
          term D l new i
  calc
    _ = ∑ D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length),
          ∑' l : Fin K → ℕ, ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i),
            ∑ i ∈ R, term D l new i := by
          apply Finset.sum_congr rfl
          intro D hD
          apply tsum_congr
          intro l
          apply Finset.sum_congr rfl
          intro new hnew
          exact hterm D l new
    _ = ∑ D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length),
          ∑' l : Fin K → ℕ, ∑ i ∈ R,
            ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i), term D l new i := by
          apply Finset.sum_congr rfl
          intro D hD
          apply tsum_congr
          intro l
          exact hswapNew D l
    _ = ∑ D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length),
          ∑ i ∈ R, ∑' l : Fin K → ℕ,
            ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i), term D l new i := by
          apply Finset.sum_congr rfl
          intro D hD
          exact hswapL D
    _ = ∑ i ∈ R,
          ∑ D : (i : Fin K) → Finset (Fin (σL.1.2.2 i).length),
            ∑' l : Fin K → ℕ,
              ∑ new : (i : Fin K) → Fin (l i) → primeBand S.x (F.a i), term D l new i := by
          rw [Finset.sum_comm]
    _ = _ := rfl

private theorem logGhost_congr_on_P {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) (P : Finset (EnvPoint S.x K))
    (f g : LogPoint S.x K → ℂ)
    (hfg : ∀ σL, (σL.1.1, σL.1.2.1) ∈ P → f σL = g σL)
    (σL : LogPoint S.x K) (hσ : (σL.1.1, σL.1.2.1) ∈ P) :
    logGhost F S ρ j f σL = logGhost F S ρ j g σL := by
  classical
  unfold logGhost
  apply Finset.sum_congr rfl
  intro D hD
  apply tsum_congr
  intro l
  apply Finset.sum_congr rfl
  intro new hnew
  by_cases hDsub : ∀ i, D i ⊆ hitIndices (σL.1.2.2 i) σL.1.1
  · simp only [if_pos hDsub]
    congr 1
    apply hfg
    exact hσ
  · simp [hDsub]

private theorem logHistoryFn_route_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (P : Finset (EnvPoint S.x K))
    (hP : ∀ t, t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1) (k : ℕ)
    (hk : k ≤ pathLength S.x) :
    ∀ σL : LogPoint S.x K, (σL.1.1, σL.1.2.1) ∈ P →
      logHistoryFn F S ρ w none none distinctWeight k σL =
        ∑ γ ∈ historyRouteFinset P k,
          logHistoryFn F S ρ w none (some γ) distinctWeight k σL := by
  induction k with
  | zero =>
      intro σL hσ
      let zσ := (σL.1.1, σL.1.2.1)
      let G := logGhost F S ρ (pathLength S.x)
        (logTrunc none (logBoundaryOut distinctWeight))
      have hbase (e : EnvPoint S.x K) :
          logHistoryFn F S ρ w none
              (some (Function.update historyDefaultPath (Fin.last (pathLength S.x)) e))
              distinctWeight 0 σL = if zσ = e then G σL else 0 := by
        have hlast :
            Function.update historyDefaultPath (Fin.last (pathLength S.x)) e
                ⟨pathLength S.x, Nat.lt_succ_self _⟩ = e := by
          have hidx :
              (⟨pathLength S.x, Nat.lt_succ_self _⟩ : Fin (pathLength S.x + 1)) =
                Fin.last (pathLength S.x) := by
            apply Fin.ext
            rfl
          rw [hidx]
          simp [Function.update]
        by_cases he : zσ = e
        · simp [logHistoryFn, logTrunc, logPathRestrict, zσ, G, he, hlast]
        · simp [logHistoryFn, logTrunc, logPathRestrict, zσ, G, he, hlast]
      rw [historyRouteFinset_zero_sum]
      simp_rw [hbase]
      change G σL = ∑ e ∈ P, if zσ = e then G σL else 0
      rw [Finset.sum_eq_single zσ]
      · simp
      · intro e he hne
        simp [Ne.symm hne]
      · intro hnot
        exact (hnot hσ).elim
  | succ k ih =>
      intro σL hkσ
      have hklt : k < pathLength S.x := by omega
      let idx := historyRouteIndex (x := S.x) (k + 1)
      let j := pathLength S.x - (k + 1)
      let zσ := (σL.1.1, σL.1.2.1)
      let routeK := historyRouteFinset P k
      let tailFn : LogPoint S.x K → ℂ := fun τ =>
        ∑ γ ∈ routeK, logHistoryFn F S ρ w none (some γ) distinctWeight k τ
      have hPvToP (τ : LogPoint S.x K)
          (hτ : (τ.1.1, τ.1.2.1) ∈ P) :
          logHistoryFn F S ρ w none none distinctWeight k τ = tailFn τ := by
        exact ih (by omega) τ hτ
      have hEdgeFun (τ : LogPoint S.x K)
          (hτ : (τ.1.1, τ.1.2.1) ∈ P) :
          logEdge F S ρ w EdgeKind.full j
              (logHistoryFn F S ρ w none none distinctWeight k) τ =
            logEdge F S ρ w EdgeKind.full j tailFn τ := by
        exact logEdge_full_congr_on_P F S ρ w j P hP
          (logHistoryFn F S ρ w none none distinctWeight k) tailFn hPvToP τ hτ
      have hbadEdge (γ : EnvPath S.x K) :
          ∀ τ, ¬ (τ.2.map Prod.snd).Nodup →
            logEdge F S ρ w EdgeKind.full j
              (logHistoryFn F S ρ w none (some γ) distinctWeight k) τ = 0 := by
        intro τ hbad
        exact logEdge_full_zero_of_badLog F S ρ w j
          (logHistoryFn F S ρ w none (some γ) distinctWeight k)
          (fun υ hυ => logHistoryFn_zero_of_badLog F S ρ w (some γ) k υ hυ) τ hbad
      have hleft :
          logHistoryFn F S ρ w none none distinctWeight (k + 1) σL =
            ∑ γ ∈ routeK,
              logGhost F S ρ j
                (logEdge F S ρ w EdgeKind.full j
                  (logHistoryFn F S ρ w none (some γ) distinctWeight k)) σL := by
        change logGhost F S ρ j
            (logEdge F S ρ w EdgeKind.full j
              (logHistoryFn F S ρ w none none distinctWeight k)) σL = _
        have hghostEdge := logGhost_congr_on_P F S ρ j P
          (logEdge F S ρ w EdgeKind.full j
            (logHistoryFn F S ρ w none none distinctWeight k))
          (logEdge F S ρ w EdgeKind.full j tailFn) hEdgeFun σL hkσ
        rw [hghostEdge]
        have hlin := logEdge_full_sum F S ρ w j routeK
          (fun γ => logHistoryFn F S ρ w none (some γ) distinctWeight k)
          P hP
        rw [hlin]
        exact congrFun (logGhost_sum_badLog F S ρ j routeK
          (fun γ => logEdge F S ρ w EdgeKind.full j
            (logHistoryFn F S ρ w none (some γ) distinctWeight k)) hbadEdge) σL
      have hfixed (γ : EnvPath S.x K) :
          (∑ e ∈ P,
            logHistoryFn F S ρ w none
              (some (Function.update γ idx e)) distinctWeight (k + 1) σL) =
            logGhost F S ρ j
              (logEdge F S ρ w EdgeKind.full j
                (logHistoryFn F S ρ w none (some γ) distinctWeight k)) σL := by
        have hselector (e : EnvPoint S.x K) :
            logHistoryFn F S ρ w none
                (some (Function.update γ idx e)) distinctWeight (k + 1) σL =
              if zσ = e then
                logGhost F S ρ j
                  (logEdge F S ρ w EdgeKind.full j
                    (logHistoryFn F S ρ w none (some γ) distinctWeight k)) σL
              else 0 := by
          have htail : ∀ t, pathLength S.x - k ≤ t.val →
              Function.update γ idx e t = γ t := by
            intro t ht
            by_cases hti : t = idx
            · subst t
              have hidx : idx.val < pathLength S.x - k := by
                simp [idx, historyRouteIndex]
                omega
              omega
            · simp [Function.update_of_ne hti]
          have hcongr := logHistoryFn_congrPath F S ρ w distinctWeight k
            (Function.update γ idx e) γ htail
          have hraw :
              logHistoryFn F S ρ w none
                  (some (Function.update γ idx e)) distinctWeight (k + 1) σL =
                if zσ = e then
                  logGhost F S ρ j
                    (logTrunc none
                      (logEdge F S ρ w EdgeKind.full j
                        (logTrunc none
                          (logHistoryFn F S ρ w none
                            (some (Function.update γ idx e)) distinctWeight k)))) σL
                else 0 := by
            simp [logHistoryFn, logTrunc, logPathRestrict, idx, historyRouteIndex,
              Function.update, zσ, j]
          calc
            _ = if zσ = e then
                  logGhost F S ρ j
                    (logTrunc none
                      (logEdge F S ρ w EdgeKind.full j
                        (logTrunc none
                          (logHistoryFn F S ρ w none
                            (some (Function.update γ idx e)) distinctWeight k)))) σL
                else 0 := hraw
            _ = if zσ = e then
                  logGhost F S ρ j
                    (logTrunc none
                      (logEdge F S ρ w EdgeKind.full j
                        (logTrunc none
                          (logHistoryFn F S ρ w none (some γ) distinctWeight k)))) σL
                else 0 := congrArg (fun H : LogPoint S.x K → ℂ =>
                  if zσ = e then
                    logGhost F S ρ j (logTrunc none
                      (logEdge F S ρ w EdgeKind.full j (logTrunc none H))) σL
                  else 0) hcongr
            _ = _ := rfl
        simp_rw [hselector]
        rw [Finset.sum_eq_single zσ]
        · simp
        · intro e he hne
          simp [Ne.symm hne]
        · intro hnot
          exact (hnot hkσ).elim
      rw [hleft]
      rw [historyRouteFinset_succ_sum P k hklt]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro γ hγ
      exact (hfixed γ).symm

private theorem initialLog_nodup_validLists {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (s : MemPoint x K) (hband : ∀ i j, s.2.1 i j ∈ primeBand x (a i))
    (hnd : ((initialLog s).map Prod.snd).Nodup) :
    ValidPrimeLists x K a s.2.1 := by
  have hflat :
      ((List.finRange K).flatMap fun i =>
        (List.finRange (slotCount x)).map fun j => s.2.1 i j).Nodup := by
    simpa [initialLog, List.map_flatMap, List.map_map, Function.comp_def] using hnd
  have hrows := (List.nodup_flatMap.mp hflat).1
  constructor
  · intro i j
    constructor
    · have hmem := hband i j
      unfold primeBand at hmem
      exact (Finset.mem_filter.mp hmem).2.1
    · exact hband i j
  · intro i j j' hne heq
    have hrow := hrows i (by simp)
    have hj : j ∈ List.finRange (slotCount x) := by simp
    have hj' : j' ∈ List.finRange (slotCount x) := by simp
    have heqidx := List.inj_on_of_nodup_map hrow hj hj' heq
    exact hne heqidx

private theorem logGhost_zero_function {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (j : ℕ) :
    logGhost F S ρ j (fun _ => 0) = fun _ => 0 := by
  funext σL
  simp [logGhost]

private theorem logEdge_full_zero_function {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (j : ℕ) :
    logEdge F S ρ w EdgeKind.full j (fun _ => 0) = fun _ => 0 := by
  funext σL
  simp [logEdge, logSym, logEdgePiece]

private theorem logHistoryFn_zero_of_path_outside {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (P : Finset (EnvPoint S.x K))
    (hP : ∀ t, t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1) (k : ℕ)
    (hk : k ≤ pathLength S.x) :
    ∀ γ : EnvPath S.x K,
      (∃ t, pathLength S.x - k ≤ t.val ∧ γ t ∉ P) →
      ∀ σL, (σL.1.1, σL.1.2.1) ∈ P →
        logHistoryFn F S ρ w none (some γ) distinctWeight k σL = 0 := by
  induction k with
  | zero =>
      intro γ hbad σL hσ
      rcases hbad with ⟨t, ht, hnot⟩
      have htval : t.val = pathLength S.x := by omega
      have htEq : t = Fin.last (pathLength S.x) := by
        apply Fin.ext
        exact htval
      have hlast : γ (Fin.last (pathLength S.x)) ∉ P := by
        simpa [htEq] using hnot
      have hneq : (σL.1.1, σL.1.2.1) ≠ γ (Fin.last (pathLength S.x)) := by
        intro heq
        exact hlast (by simpa [heq] using hσ)
      have hlastIdx :
          (⟨pathLength S.x, Nat.lt_succ_self _⟩ : Fin (pathLength S.x + 1)) =
            Fin.last (pathLength S.x) := by
        apply Fin.ext
        rfl
      have hneq' : (σL.1.1, σL.1.2.1) ≠ γ
          ⟨pathLength S.x, Nat.lt_succ_self _⟩ := by
        simpa [hlastIdx] using hneq
      simp [logHistoryFn, logTrunc, logPathRestrict, hneq']
  | succ k ih =>
      intro γ hbad σL hσ
      have hklt : k < pathLength S.x := by omega
      let idx := historyRouteIndex (x := S.x) (k + 1)
      let j := pathLength S.x - (k + 1)
      have hIdxFin :
          (⟨j, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ : Fin (pathLength S.x + 1)) = idx := by
        apply Fin.ext
        simp [idx, j, historyRouteIndex]
      have hbad' := hbad
      rcases hbad' with ⟨t, ht, hnot⟩
      by_cases hcur : (σL.1.1, σL.1.2.1) = γ idx
      · have hcurP : γ idx ∈ P := by simpa [hcur] using hσ
        have hti : t ≠ idx := by
          intro heq
          subst t
          exact hnot hcurP
        have htTail : pathLength S.x - k ≤ t.val := by
          have hneVal : t.val ≠ idx.val := by
            intro heq
            apply hti
            exact Fin.ext heq
          change idx.val ≤ t.val at ht
          have hltVal : idx.val < t.val := lt_of_le_of_ne ht (Ne.symm hneVal)
          have hidxplus : idx.val + 1 = pathLength S.x - k := by
            simp [idx, historyRouteIndex]
            omega
          omega
        have hbadTail : ∃ t, pathLength S.x - k ≤ t.val ∧ γ t ∉ P :=
          ⟨t, htTail, hnot⟩
        have hrecZero (τ : LogPoint S.x K)
            (hτ : (τ.1.1, τ.1.2.1) ∈ P) :
            logHistoryFn F S ρ w none (some γ) distinctWeight k τ = 0 :=
          ih (by omega) γ hbadTail τ hτ
        have hEdgeZero (τ : LogPoint S.x K)
            (hτ : (τ.1.1, τ.1.2.1) ∈ P) :
            logEdge F S ρ w EdgeKind.full j
                (logHistoryFn F S ρ w none (some γ) distinctWeight k) τ = 0 := by
          rw [logEdge_full_congr_on_P F S ρ w j P hP
            (logHistoryFn F S ρ w none (some γ) distinctWeight k) (fun _ => 0)
            (fun υ hυ => hrecZero υ hυ) τ hτ]
          exact congrFun (logEdge_full_zero_function F S ρ w j) τ
        have hghostZero := logGhost_congr_on_P F S ρ j P
          (logEdge F S ρ w EdgeKind.full j
            (logHistoryFn F S ρ w none (some γ) distinctWeight k)) (fun _ => 0)
          hEdgeZero σL hσ
        have hfinal :
            logGhost F S ρ j
              (logEdge F S ρ w EdgeKind.full j
                (logHistoryFn F S ρ w none (some γ) distinctWeight k)) σL = 0 :=
          hghostZero.trans (congrFun (logGhost_zero_function F S ρ j) σL)
        have hfinalWrapped :
            logGhost F S ρ j
              (logTrunc none
                (logEdge F S ρ w EdgeKind.full j
                  (logTrunc none
                    (logHistoryFn F S ρ w none (some γ) distinctWeight k)))) σL = 0 := by
          change logGhost F S ρ j
              (logEdge F S ρ w EdgeKind.full j
                (logHistoryFn F S ρ w none (some γ) distinctWeight k)) σL = 0
          exact hfinal
        have hcurrent : (σL.1.1, σL.1.2.1) = γ
            ⟨j, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
          simpa [hIdxFin] using hcur
        simpa [logHistoryFn, logTrunc, logPathRestrict, j, hcurrent] using hfinalWrapped
      · have hcur' : (σL.1.1, σL.1.2.1) ≠ γ
            ⟨j, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
          simpa [hIdxFin] using hcur
        simp [logHistoryFn, logTrunc, logPathRestrict, j, hcur']

private noncomputable def historyInitialPrimeLists {x : ℝ} {K : ℕ}
    (a : Fin K → ℝ) : Finset (PrimeLists x K) :=
  Fintype.piFinset fun i : Fin K =>
    Fintype.piFinset fun j : Fin (slotCount x) => primeBand x (a i)

private noncomputable def historyInitialStates {x : ℝ} {K : ℕ}
    (a : Fin K → ℝ) : Finset (MemPoint x K) :=
  (historyInitialPrimeLists a).image fun p => ((1, 0), p, fun _ => [])

private noncomputable def historyInitialLogs {x : ℝ} {K : ℕ}
    (a : Fin K → ℝ) : Finset (LogPoint x K) :=
  (historyInitialStates a).image fun s => (s, initialLog s)

private theorem mem_historyInitialLogs {x : ℝ} {K : ℕ} (a : Fin K → ℝ)
    (σL : LogPoint x K) :
    σL ∈ historyInitialLogs a ↔
      σL.1.1 = (1, 0) ∧ (∀ i, σL.1.2.2 i = []) ∧
        σL.2 = initialLog σL.1 ∧
        (∀ i j, σL.1.2.1 i j ∈ primeBand x (a i)) := by
  classical
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨s, hs, hσ⟩
    rcases Finset.mem_image.mp hs with ⟨p, hp, rfl⟩
    subst σL
    constructor
    · rfl
    constructor
    · intro i
      rfl
    constructor
    · rfl
    · simpa [historyInitialPrimeLists, Fintype.mem_piFinset] using hp
  · rintro ⟨hz, hmem, hlog, hband⟩
    apply Finset.mem_image.mpr
    refine ⟨σL.1, ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨σL.1.2.1, ?_, ?_⟩
      · simpa [historyInitialPrimeLists, Fintype.mem_piFinset] using hband
      · exact Prod.ext hz.symm (Prod.ext rfl (funext hmem).symm)
    · exact Prod.ext rfl hlog.symm

/-- The initial log-inner-product coefficient is supported on a finite set of valid
boundary states. -/
theorem pd_life_b_initialLogSupport_finite {K : ℕ} (F : PDFix K) (S : PDScale) :
    {σL : LogPoint S.x K |
      (memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL) ≠ 0}.Finite := by
  classical
  let T : Finset (LogPoint S.x K) := historyInitialLogs F.a
  have hInitFacts (σL : LogPoint S.x K)
      (hμ : memMeasure F S σL.1 ≠ 0) (hb : logBoundaryIn σL ≠ 0) :
      σL ∈ T := by
    have hlog : σL.2 = initialLog σL.1 := by
      by_contra hn
      apply hb
      simp [logBoundaryIn, hn]
    have hboundary : σL.1.1 = (1, 0) ∧ (∀ i, σL.1.2.2 i = []) := by
      by_contra hn
      apply hb
      simp [logBoundaryIn, hlog, memBoundary, hn]
    have hvalid : MemValid F S σL.1 := by
      by_contra hn
      apply hμ
      simp [memMeasure, hn]
    apply (mem_historyInitialLogs F.a σL).2
    exact ⟨hboundary.1, hboundary.2, hlog, hvalid.2.1⟩
  have hsubset :
      {σL : LogPoint S.x K |
        (memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL) ≠ 0} ⊆ (T : Set _) := by
    intro σL hσ
    have hμ : memMeasure F S σL.1 ≠ 0 := by
      intro hzero
      apply hσ
      simp [hzero]
    have hb : logBoundaryIn σL ≠ 0 := by
      intro hzero
      apply hσ
      simp [hzero]
    exact hInitFacts σL hμ hb
  exact T.finite_toSet.subset hsubset

/-- Reduce any logged history inner product to a finite sum over its supported initial
boundary states. -/
theorem pd_life_b_logInner_tsum_eq_finite_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (g : LogPoint S.x K → ℂ) :
    (∑' σL : LogPoint S.x K,
      ((memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL)) * g σL) =
      ∑ σL ∈ (pd_life_b_initialLogSupport_finite F S).toFinset,
        ((memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL)) * g σL := by
  classical
  apply tsum_eq_sum
  intro σL hσ
  have hnot : σL ∉
      {τ : LogPoint S.x K |
        (memMeasure F S τ.1 : ℂ) * star (logBoundaryIn τ) ≠ 0} := by
    simpa [Set.Finite.mem_toFinset] using hσ
  have hzero : (memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL) = 0 := by
    by_contra hn
    exact hnot hn
  change ((memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL)) * g σL = 0
  rw [hzero]
  simp

/-- Expand `memHistory` as a finite sum over the supported initial boundary logs. -/
theorem pd_life_b_memHistory_initialLog_sum {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (B : Option ℕ) (γ : Option (EnvPath S.x K))
    (W : BirthLog K → ℂ) :
    memHistory F S ρ w B γ W =
      ∑ σL ∈ (pd_life_b_initialLogSupport_finite F S).toFinset,
        ((memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL)) *
          logHistoryFn F S ρ w B γ W (pathLength S.x) σL := by
  unfold memHistory logInner
  exact pd_life_b_logInner_tsum_eq_finite_sum F S
    (logHistoryFn F S ρ w B γ W (pathLength S.x))

private theorem logGhost_zero_of_boundary_pos_ne_e1 {K : ℕ} (F : PDFix K)
    (S : PDScale) (ρ : ℝ) (j : ℕ) (σL : LogPoint S.x K)
    (hpos : σL.1.1 ≠ (1, 0)) :
    logGhost F S ρ j (logBoundaryOut distinctWeight) σL = 0 := by
  classical
  unfold logGhost
  apply Finset.sum_eq_zero
  intro D hD
  apply tsum_zero_of_eq_zero
  intro l
  apply Finset.sum_eq_zero
  intro new hnew
  by_cases hDsub : ∀ i, D i ⊆ hitIndices (σL.1.2.2 i) σL.1.1
  · have hboundary :
        logBoundaryOut distinctWeight
          (((σL.1.1, σL.1.2.1, fun i =>
            removeIndices (σL.1.2.2 i) (D i) ++
              List.ofFn fun k : Fin (l i) => anchorAt (new i k) σL.1.1),
            σL.2 ++ (List.finRange K).flatMap fun i =>
              List.ofFn fun k : Fin (l i) =>
                (BirthAddress.ghost j i k.val, (new i k : ℕ)))) = 0 := by
      simp [logBoundaryOut, memBoundary, hpos]
    simp [hDsub, hboundary]
  · simp [hDsub]

private theorem logHistoryFn_zero_of_last_not_e1 {K : ℕ} (F : PDFix K)
    (S : PDScale) (ρ : ℝ) (w : ArchRoot) (γ : EnvPath S.x K) (k : ℕ)
    (hlast : (γ (Fin.last (pathLength S.x))).1 ≠ (1, 0)) :
    logHistoryFn F S ρ w none (some γ) distinctWeight k = fun _ => 0 := by
  induction k with
  | zero =>
      funext σL
      by_cases hmatch : (σL.1.1, σL.1.2.1) = γ (Fin.last (pathLength S.x))
      · have hpos : σL.1.1 ≠ (1, 0) := by
          intro hz
          apply hlast
          exact (congrArg Prod.fst hmatch).symm.trans hz
        have hghost := logGhost_zero_of_boundary_pos_ne_e1 F S ρ
          (pathLength S.x) σL hpos
        have hlastIdx :
            (⟨pathLength S.x, Nat.lt_succ_self _⟩ : Fin (pathLength S.x + 1)) =
              Fin.last (pathLength S.x) := by
          apply Fin.ext
          rfl
        have hmatch' : (σL.1.1, σL.1.2.1) =
            γ ⟨pathLength S.x, Nat.lt_succ_self _⟩ := by
          simpa [hlastIdx] using hmatch
        have hghostWrapped :
            logGhost F S ρ (pathLength S.x)
              (logTrunc none (logBoundaryOut distinctWeight)) σL = 0 := by
          change logGhost F S ρ (pathLength S.x)
            (logBoundaryOut distinctWeight) σL = 0
          exact hghost
        simpa [logHistoryFn, logTrunc, logPathRestrict, hmatch'] using hghostWrapped
      · have hlastIdx :
            (⟨pathLength S.x, Nat.lt_succ_self _⟩ : Fin (pathLength S.x + 1)) =
              Fin.last (pathLength S.x) := by
          apply Fin.ext
          rfl
        have hmatch' : (σL.1.1, σL.1.2.1) ≠
            γ ⟨pathLength S.x, Nat.lt_succ_self _⟩ := by
          simpa [hlastIdx] using hmatch
        simp [logHistoryFn, logTrunc, logPathRestrict, hmatch']
  | succ k ih =>
      funext σL
      have hrec := ih
      have hedge : logEdge F S ρ w EdgeKind.full
          (pathLength S.x - (k + 1))
          (logTrunc none (logHistoryFn F S ρ w none (some γ) distinctWeight k)) =
            (fun _ => 0) := by
        rw [hrec]
        exact logEdge_full_zero_function F S ρ w _
      have hghost : logGhost F S ρ (pathLength S.x - (k + 1))
          (logTrunc none
            (logEdge F S ρ w EdgeKind.full (pathLength S.x - (k + 1))
              (logTrunc none
                (logHistoryFn F S ρ w none (some γ) distinctWeight k)))) =
            (fun _ => 0) := by
        have hrec' : logHistoryFn F S ρ w none (some γ) distinctWeight k =
            (fun _ => 0) := hrec
        rw [hrec']
        change logGhost F S ρ (pathLength S.x - (k + 1))
          (logTrunc none
            (logEdge F S ρ w EdgeKind.full (pathLength S.x - (k + 1))
              (fun _ => 0))) = (fun _ => 0)
        rw [logEdge_full_zero_function]
        change logGhost F S ρ (pathLength S.x - (k + 1)) (fun _ => 0) = (fun _ => 0)
        exact logGhost_zero_function F S ρ _
      simp [logHistoryFn, logTrunc, logPathRestrict, hghost]

/-- `t2:pd.history-paths` (new node) — PD 04:234-246.  Exact decomposition of the distinct
history by the sequence of positions and active lists at the visits (ghosts do not move them;
the edges move along the path; distinct initial entries make every visit list valid). -/
theorem pd_life_b_history_paths (δ c₁ c₂ : ℝ) (hδ : 0 < δ) (hc₁ : 0 < c₁) :
    ∀ (K : ℕ) (F : PDFix K), F.Valid → ∀ ρ : ℝ, IsMemoryRho F.q_d ρ →
      ∃ x₀ : ℝ, 2 ≤ x₀ ∧ ∀ S : PDScale, S.Valid K δ c₁ c₂ → x₀ ≤ S.x →
        ∀ w : ArchRoot, w.InRegion S →
          historyDistinct F S ρ w =
            ∑' γ : EnvPath S.x K,
              if IsEnvPathAdmissible F S γ then memHistory F S ρ w none (some γ) distinctWeight else 0 := by
  classical
  intro K F hF ρ hρ
  refine ⟨2, by norm_num, ?_⟩
  intro S hS hx0 w hw
  classical
  rcases hS with ⟨hxS, hHm, hHn, _, _, hY, hpad⟩
  have hxpos : 0 < S.x := by linarith
  have hpowpos : 0 < Real.rpow S.x δ := Real.rpow_pos_of_pos hxpos _
  have hHmpos : 0 < S.Hm := lt_of_lt_of_le hpowpos hHm
  have hHnpos : 0 < S.Hn := lt_of_lt_of_le hpowpos hHn
  have hYpos : 0 < S.Y := by
    unfold dyadicScales at hY
    rcases Finset.mem_filter.mp hY with ⟨himage, _⟩
    rcases Finset.mem_image.mp himage with ⟨n, _, hEq⟩
    rw [← hEq]
    positivity
  have hd0pos : 0 < (S.d₀ : ℝ) := by
    unfold padScales at hpad
    rcases Finset.mem_image.mp hpad with ⟨n, _, hEq⟩
    rw [← hEq]
    positivity
  have hUpos : 0 < S.U := by
    dsimp [PDScale.U, PDScale.H]
    exact mul_pos (mul_pos hd0pos hYpos) hHmpos
  have hVpos : 0 < S.V := by
    simpa [PDScale.V] using hHnpos
  have hlogpos : 0 < Real.log S.x := Real.log_pos (by linarith [hxS])
  let rArg := Real.rpow (Real.log S.x) (1 / 2 : ℝ) / 2
  have hrArg : 0 < rArg := by
    dsimp [rArg]
    exact div_pos (Real.rpow_pos_of_pos hlogpos _) (by norm_num)
  have hRpos : 0 < momentR S.x := by
    change 0 < ⌈rArg⌉₊
    by_contra hR
    have hRzero : (⌈rArg⌉₊ : ℕ) = 0 := by omega
    have hceil : rArg ≤ (⌈rArg⌉₊ : ℕ) := Nat.le_ceil rArg
    rw [hRzero] at hceil
    have hceil' : rArg ≤ 0 := by exact_mod_cast hceil
    exact (not_le_of_gt hrArg) hceil'
  have hNpos : 0 < pathLength S.x := by
    dsimp [pathLength]
    exact Nat.mul_pos (by omega) hRpos
  have hwRegion := hw
  rcases hw with ⟨hu1, hu2, hv1, hv2, _, _⟩
  have he1box : envBox S w (1, 0) := by
    simpa [envBox, ArchRoot.tau] using ⟨hu1, hu2, hv1, hv2⟩
  have hPfin := envPoint_valid_box_finite F S w hUpos hVpos hwRegion
  let P : Finset (EnvPoint S.x K) := hPfin.toFinset
  have hP (t : EnvPoint S.x K) :
      t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1 := by
    simp [P]
  let R : Finset (EnvPath S.x K) := historyRouteFinset P (pathLength S.x)
  let T : Finset (LogPoint S.x K) := historyInitialLogs F.a
  let coeff (σL : LogPoint S.x K) : ℂ :=
    (memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL)
  have hInitFacts (σL : LogPoint S.x K)
      (hμ : memMeasure F S σL.1 ≠ 0) (hb : logBoundaryIn σL ≠ 0) :
      σL ∈ T ∧ MemValid F S σL.1 ∧
        σL.1.1 = (1, 0) ∧ (∀ i, σL.1.2.2 i = []) ∧
        σL.2 = initialLog σL.1 := by
    have hlog : σL.2 = initialLog σL.1 := by
      by_contra hn
      apply hb
      simp [logBoundaryIn, hn]
    have hboundary : σL.1.1 = (1, 0) ∧ (∀ i, σL.1.2.2 i = []) := by
      by_contra hn
      apply hb
      simp [logBoundaryIn, hlog, memBoundary, hn]
    have hvalid : MemValid F S σL.1 := by
      by_contra hn
      apply hμ
      simp [memMeasure, hn]
    have hmemT : σL ∈ T := by
      apply (mem_historyInitialLogs F.a σL).2
      exact ⟨hboundary.1, hboundary.2, hlog, hvalid.2.1⟩
    exact ⟨hmemT, hvalid, hboundary.1, hboundary.2, hlog⟩
  have hcoeffzero : ∀ σL, σL ∉ T → coeff σL = 0 := by
    intro σL hσ
    by_cases hμ : memMeasure F S σL.1 = 0
    · simp [coeff, hμ]
    · by_cases hb : logBoundaryIn σL = 0
      · simp [coeff, hb]
      · exact (hσ (hInitFacts σL hμ hb).1).elim
  have hroutePoint (σL : LogPoint S.x K) :
      coeff σL * logHistoryFn F S ρ w none none distinctWeight (pathLength S.x) σL =
        ∑ γ ∈ R, coeff σL *
          logHistoryFn F S ρ w none (some γ) distinctWeight (pathLength S.x) σL := by
    by_cases hμ : memMeasure F S σL.1 = 0
    · simp [coeff, hμ]
    · by_cases hb : logBoundaryIn σL = 0
      · simp [coeff, hb]
      · obtain ⟨hT, hvalid, hz, hmem, hlog⟩ := hInitFacts σL hμ hb
        by_cases hnd : (σL.2.map Prod.snd).Nodup
        · have hndInit : ((initialLog σL.1).map Prod.snd).Nodup := by
            simpa [hlog] using hnd
          have hband : ∀ i j, σL.1.2.1 i j ∈ primeBand S.x (F.a i) := hvalid.2.1
          have hLists := initialLog_nodup_validLists F.a σL.1 hband hndInit
          have hEnv : EnvValid F S (σL.1.1, σL.1.2.1) := by
            refine ⟨?_, hLists⟩
            norm_num [hz, Int.gcd]
          have hsource : (σL.1.1, σL.1.2.1) ∈ P :=
            (hP _).2 ⟨hEnv, by simpa [hz] using he1box⟩
          have hroute := logHistoryFn_route_sum F S ρ w P hP
            (pathLength S.x) le_rfl σL hsource
          calc
            _ = coeff σL *
                (∑ γ ∈ R,
                  logHistoryFn F S ρ w none (some γ) distinctWeight
                    (pathLength S.x) σL) := congrArg (fun z => coeff σL * z) hroute
            _ = _ := by rw [Finset.mul_sum]
        · have hzeroNone :=
            logHistoryFn_zero_of_badLog F S ρ w none (pathLength S.x) σL hnd
          have hzeroPath (γ : EnvPath S.x K) :=
            logHistoryFn_zero_of_badLog F S ρ w (some γ) (pathLength S.x) σL hnd
          simp [hzeroNone, hzeroPath]
  have hfiniteDecomp :
      historyDistinct F S ρ w =
        ∑ γ ∈ R, memHistory F S ρ w none (some γ) distinctWeight := by
    unfold historyDistinct memHistory logInner
    change (∑' σL, coeff σL *
          logHistoryFn F S ρ w none none distinctWeight (pathLength S.x) σL) = _
    calc
      _ = ∑' σL, ∑ γ ∈ R, coeff σL *
            logHistoryFn F S ρ w none (some γ) distinctWeight (pathLength S.x) σL := by
          apply tsum_congr
          intro σL
          exact hroutePoint σL
      _ = ∑ γ ∈ R, ∑' σL, coeff σL *
            logHistoryFn F S ρ w none (some γ) distinctWeight (pathLength S.x) σL :=
          tsum_sum_finite_support T R
            (fun σL γ => coeff σL *
              logHistoryFn F S ρ w none (some γ) distinctWeight (pathLength S.x) σL)
            (by
              intro γ σL hσ
              simp [hcoeffzero σL hσ])
      _ = _ := rfl
  have hbadOutside (γ : EnvPath S.x K) (hγ : γ ∉ R) :
      ∃ t, pathLength S.x - pathLength S.x ≤ t.val ∧ γ t ∉ P := by
    by_contra hn
    have hall : ∀ t, γ t ∈ P := by
      intro t
      by_contra hnot
      exact hn ⟨t, by omega, hnot⟩
    have hroute : γ ∈ historyRouteFinset P (pathLength S.x) := by
      rw [mem_historyRouteFinset]
      constructor
      · intro t ht
        exact hall t
      · intro t ht
        have ht0 : t.val < 0 := by simpa using ht
        omega
    exact hγ (by simpa [R] using hroute)
  have hmemZeroOutside (γ : EnvPath S.x K) (hγ : γ ∉ R) :
      memHistory F S ρ w none (some γ) distinctWeight = 0 := by
    have hbad := hbadOutside γ hγ
    unfold memHistory logInner
    apply tsum_zero_of_eq_zero
    intro σL
    by_cases hT : σL ∈ T
    · rcases (mem_historyInitialLogs F.a σL).mp hT with ⟨hz, hmem, hlog, hband⟩
      by_cases hnd : (σL.2.map Prod.snd).Nodup
      · have hndInit : ((initialLog σL.1).map Prod.snd).Nodup := by
          simpa [hlog] using hnd
        have hLists := initialLog_nodup_validLists F.a σL.1 hband hndInit
        have hEnv : EnvValid F S (σL.1.1, σL.1.2.1) := by
          refine ⟨?_, hLists⟩
          norm_num [hz, Int.gcd]
        have hsource : (σL.1.1, σL.1.2.1) ∈ P :=
          (hP _).2 ⟨hEnv, by simpa [hz] using he1box⟩
        have hzero := logHistoryFn_zero_of_path_outside F S ρ w P hP
          (pathLength S.x) le_rfl γ hbad σL hsource
        change coeff σL *
          logHistoryFn F S ρ w none (some γ) distinctWeight (pathLength S.x) σL = 0
        rw [hzero]
        simp
      · have hzero :=
          logHistoryFn_zero_of_badLog F S ρ w (some γ) (pathLength S.x) σL hnd
        change coeff σL *
          logHistoryFn F S ρ w none (some γ) distinctWeight (pathLength S.x) σL = 0
        rw [hzero]
        simp
    · have hc :
          (memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL) = 0 := by
        simpa [coeff] using hcoeffzero σL hT
      change ((memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL)) *
        logHistoryFn F S ρ w none (some γ) distinctWeight (pathLength S.x) σL = 0
      rw [hc]
      simp
  have hrestrictedZeroNonAdm (γ : EnvPath S.x K) (hγ : γ ∈ R)
      (hAdm : ¬ IsEnvPathAdmissible F S γ) :
      memHistory F S ρ w none (some γ) distinctWeight = 0 := by
    have hroute := (mem_historyRouteFinset P (pathLength S.x) γ).mp
      (by simpa [R] using hγ)
    have hvalidAll : ∀ j, EnvValid F S (γ j) := by
      intro j
      have hj : pathLength S.x - pathLength S.x ≤ j.val := by omega
      exact (hP (γ j)).mp (hroute.1 j hj) |>.1
    have hfnzero (σL : LogPoint S.x K) (hT : σL ∈ T) :
        logHistoryFn F S ρ w none (some γ) distinctWeight (pathLength S.x) σL = 0 := by
      rcases (mem_historyInitialLogs F.a σL).mp hT with ⟨hz, _, _, _⟩
      by_cases hstart :
          (γ ⟨0, Nat.zero_lt_succ (pathLength S.x)⟩).1 = (1, 0)
      · by_cases hlast :
            (γ (Fin.last (pathLength S.x))).1 = (1, 0)
        · exact (hAdm ⟨hvalidAll, by simpa using hstart, hlast⟩).elim
        · exact congrFun (logHistoryFn_zero_of_last_not_e1 F S ρ w γ
            (pathLength S.x) hlast) σL
      · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hNpos.ne'
        rw [hn]
        have hcurrent : (σL.1.1, σL.1.2.1) ≠ γ ⟨0, by omega⟩ := by
          intro heq
          apply hstart
          exact (congrArg Prod.fst heq).symm.trans hz
        have hcurrent0 : (σL.1.1, σL.1.2.1) ≠ γ 0 := by
          simpa using hcurrent
        simp [logHistoryFn, logTrunc, logPathRestrict, hcurrent0, hn]
    unfold memHistory logInner
    apply tsum_zero_of_eq_zero
    intro σL
    by_cases hT : σL ∈ T
    · change coeff σL *
        logHistoryFn F S ρ w none (some γ) distinctWeight (pathLength S.x) σL = 0
      rw [hfnzero σL hT]
      simp
    · have hc :
          (memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL) = 0 := by
        simpa [coeff] using hcoeffzero σL hT
      change ((memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL)) *
        logHistoryFn F S ρ w none (some γ) distinctWeight (pathLength S.x) σL = 0
      rw [hc]
      simp
  have hsumAdm :
      (∑ γ ∈ R, memHistory F S ρ w none (some γ) distinctWeight) =
        ∑ γ ∈ R,
          if IsEnvPathAdmissible F S γ then
            memHistory F S ρ w none (some γ) distinctWeight else 0 := by
    apply Finset.sum_congr rfl
    intro γ hγ
    by_cases hAdm : IsEnvPathAdmissible F S γ
    · simp [hAdm]
    · simp [hAdm, hrestrictedZeroNonAdm γ hγ hAdm]
  have htsumAll :
      (∑' γ : EnvPath S.x K,
        if IsEnvPathAdmissible F S γ then
          memHistory F S ρ w none (some γ) distinctWeight else 0) =
        ∑ γ ∈ R,
          if IsEnvPathAdmissible F S γ then
            memHistory F S ρ w none (some γ) distinctWeight else 0 := by
    apply tsum_eq_sum
    intro γ hγ
    by_cases hAdm : IsEnvPathAdmissible F S γ
    · simp [hAdm, hmemZeroOutside γ hγ]
    · simp [hAdm]
  calc
    historyDistinct F S ρ w =
        ∑ γ ∈ R, memHistory F S ρ w none (some γ) distinctWeight := hfiniteDecomp
    _ = ∑ γ ∈ R,
          if IsEnvPathAdmissible F S γ then
            memHistory F S ρ w none (some γ) distinctWeight else 0 := hsumAdm
    _ = _ := htsumAll.symm


private theorem pd_life_b_logTrunc_sum {K : ℕ} (S : PDScale) (B : Option ℕ)
    {ι : Type*} (R : Finset ι) (f : ι → LogPoint S.x K → ℂ) :
    logTrunc B (fun τ => ∑ i ∈ R, f i τ) =
      fun τ => ∑ i ∈ R, logTrunc B (f i) τ := by
  funext τ
  cases B with
  | none => rfl
  | some b =>
      by_cases h : memSize τ.1 ≤ b <;> simp [logTrunc, h]

private theorem pd_life_b_logHistoryFn_zero_of_badLog_nat {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (b : ℕ)
    (γ : Option (EnvPath S.x K)) :
    ∀ k σL, ¬ (σL.2.map Prod.snd).Nodup →
      logHistoryFn F S ρ w (some b) γ distinctWeight k σL = 0 := by
  intro k
  induction k with
  | zero =>
      intro σL hbad
      have hboundary : ∀ τ : LogPoint S.x K, ¬ (τ.2.map Prod.snd).Nodup →
          logBoundaryOut distinctWeight τ = 0 := by
        intro τ hτ
        simp [logBoundaryOut, distinctWeight, hτ]
      have hghostTrunc :
          logGhost F S ρ (pathLength S.x)
            (logTrunc (some b) (logBoundaryOut distinctWeight)) σL = 0 := by
        exact logGhost_zero_of_badLog F S ρ (pathLength S.x)
          (logTrunc (some b) (logBoundaryOut distinctWeight))
          (by
            intro τ hτ
            by_cases hcut : memSize τ.1 ≤ b <;>
              simp [logTrunc, hcut, hboundary τ hτ]) σL hbad
      cases γ with
      | none =>
          by_cases hcut : memSize σL.1 ≤ b
          · simpa [logHistoryFn, logTrunc, logPathRestrict, hcut] using hghostTrunc
          · simp [logHistoryFn, logTrunc, logPathRestrict, hcut]
      | some path =>
          by_cases hcut : memSize σL.1 ≤ b
          · simp [logHistoryFn, logTrunc, logPathRestrict, hcut, hghostTrunc]
          · simp [logHistoryFn, logTrunc, logPathRestrict, hcut]
  | succ k ih =>
      intro σL hbad
      have hf : ∀ τ, ¬ (τ.2.map Prod.snd).Nodup →
          logTrunc (some b) (logHistoryFn F S ρ w (some b) γ distinctWeight k) τ = 0 := by
        intro τ hτ
        simp [logTrunc, ih τ hτ]
      have hEdge : ∀ τ, ¬ (τ.2.map Prod.snd).Nodup →
          logEdge F S ρ w EdgeKind.full (pathLength S.x - (k + 1))
            (logTrunc (some b) (logHistoryFn F S ρ w (some b) γ distinctWeight k)) τ = 0 := by
        intro τ hτ
        exact logEdge_full_zero_of_badLog F S ρ w (pathLength S.x - (k + 1))
          (logTrunc (some b) (logHistoryFn F S ρ w (some b) γ distinctWeight k)) hf τ hτ
      have hghostTrunc :
          logGhost F S ρ (pathLength S.x - (k + 1))
            (logTrunc (some b)
              (logEdge F S ρ w EdgeKind.full (pathLength S.x - (k + 1))
                (logTrunc (some b) (logHistoryFn F S ρ w (some b) γ distinctWeight k)))) σL = 0 := by
        exact logGhost_zero_of_badLog F S ρ (pathLength S.x - (k + 1))
          (logTrunc (some b)
            (logEdge F S ρ w EdgeKind.full (pathLength S.x - (k + 1))
              (logTrunc (some b) (logHistoryFn F S ρ w (some b) γ distinctWeight k))))
          (by
            intro τ hτ
            by_cases hcut : memSize τ.1 ≤ b <;>
              simp [logTrunc, hcut, hEdge τ hτ]) σL hbad
      cases γ with
      | none =>
          by_cases hcut : memSize σL.1 ≤ b
          · simpa [logHistoryFn, logTrunc, logPathRestrict, hcut] using hghostTrunc
          · simp [logHistoryFn, logTrunc, logPathRestrict, hcut]
      | some path =>
          by_cases hcut : memSize σL.1 ≤ b
          · simp [logHistoryFn, logTrunc, logPathRestrict, hcut, hghostTrunc]
          · simp [logHistoryFn, logTrunc, logPathRestrict, hcut]

/-- A repeated prime in a birth log is annihilated by the cutoff history as well. -/
theorem pd_life_b_logHistoryFn_zero_of_badLog_cutoff {K : ℕ} (F : PDFix K)
    (S : PDScale) (ρ : ℝ) (w : ArchRoot) (b : ℕ)
    (γ : Option (EnvPath S.x K)) (k : ℕ) (σL : LogPoint S.x K)
    (hbad : ¬ (σL.2.map Prod.snd).Nodup) :
    logHistoryFn F S ρ w (some b) γ distinctWeight k σL = 0 :=
  pd_life_b_logHistoryFn_zero_of_badLog_nat F S ρ w b γ k σL hbad

/-- The outer path restriction at stage k forces the current endpoint to be visit N-k. -/
theorem pd_life_b_logHistoryFn_zero_off_path_visit {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (B : Option ℕ) (γ : EnvPath S.x K)
    (W : BirthLog K → ℂ) (k : ℕ) (hk : k ≤ pathLength S.x)
    (σL : LogPoint S.x K)
    (hoff : (σL.1.1, σL.1.2.1) ≠
      γ ⟨pathLength S.x - k, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) :
    logHistoryFn F S ρ w B (some γ) W k σL = 0 := by
  cases k with
  | zero =>
      have hoff0 : (σL.1.1, σL.1.2.1) ≠
          γ ⟨pathLength S.x, Nat.lt_succ_self _⟩ := by
        simpa using hoff
      cases B <;> simp [logHistoryFn, logTrunc, logPathRestrict, hoff0]
  | succ k =>
      cases B <;> simp [logHistoryFn, logTrunc, logPathRestrict, hoff]

private theorem pd_life_b_logHistoryFn_congrPath_nat {K : ℕ} (F : PDFix K)
    (S : PDScale) (ρ : ℝ) (w : ArchRoot) (b : ℕ)
    (W : BirthLog K → ℂ) (k : ℕ) (γ γ' : EnvPath S.x K)
    (hγ : ∀ j, pathLength S.x - k ≤ j.val → γ j = γ' j) :
    logHistoryFn F S ρ w (some b) (some γ) W k =
      logHistoryFn F S ρ w (some b) (some γ') W k := by
  induction k with
  | zero =>
      have hlast : γ (Fin.last (pathLength S.x)) = γ' (Fin.last (pathLength S.x)) :=
        hγ _ (by simp)
      have hlast' : γ ⟨pathLength S.x, Nat.lt_succ_self _⟩ =
          γ' ⟨pathLength S.x, Nat.lt_succ_self _⟩ := by
        simpa [Fin.last] using hlast
      funext σL
      simp [logHistoryFn, logTrunc, logPathRestrict, hlast']
  | succ k ih =>
      let idx := historyRouteIndex (x := S.x) (k + 1)
      have hcur : γ idx = γ' idx := hγ idx (by simp [idx, historyRouteIndex])
      have hcur' : γ ⟨pathLength S.x - (k + 1), by omega⟩ =
          γ' ⟨pathLength S.x - (k + 1), by omega⟩ := by
        simpa [idx, historyRouteIndex] using hcur
      have htail : ∀ j, pathLength S.x - k ≤ j.val → γ j = γ' j := by
        intro j hj
        exact hγ j (by omega)
      have hrec := ih htail
      funext σL
      simp only [logHistoryFn, logTrunc]
      rw [hrec]
      simp [logPathRestrict, hcur']

private theorem pd_life_b_logHistoryFn_route_sum_nat {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (b : ℕ)
    (P : Finset (EnvPoint S.x K))
    (hP : ∀ t, t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1) (k : ℕ)
    (hk : k ≤ pathLength S.x) :
    ∀ σL : LogPoint S.x K, (σL.1.1, σL.1.2.1) ∈ P →
      logHistoryFn F S ρ w (some b) none distinctWeight k σL =
        ∑ γ ∈ historyRouteFinset P k,
          logHistoryFn F S ρ w (some b) (some γ) distinctWeight k σL := by
  induction k with
  | zero =>
      intro σL hσ
      let zσ := (σL.1.1, σL.1.2.1)
      let G := logTrunc (some b)
        (logGhost F S ρ (pathLength S.x)
          (logTrunc (some b) (logBoundaryOut distinctWeight)))
      have hbase (e : EnvPoint S.x K) :
          logHistoryFn F S ρ w (some b)
              (some (Function.update historyDefaultPath (Fin.last (pathLength S.x)) e))
              distinctWeight 0 σL = if zσ = e then G σL else 0 := by
        have hlast :
            Function.update historyDefaultPath (Fin.last (pathLength S.x)) e
                ⟨pathLength S.x, Nat.lt_succ_self _⟩ = e := by
          have hidx :
              (⟨pathLength S.x, Nat.lt_succ_self _⟩ : Fin (pathLength S.x + 1)) =
                Fin.last (pathLength S.x) := by
            apply Fin.ext
            rfl
          rw [hidx]
          simp [Function.update]
        by_cases he : zσ = e
        · simp [logHistoryFn, logTrunc, logPathRestrict, zσ, G, he, hlast]
        · simp [logHistoryFn, logTrunc, logPathRestrict, zσ, G, he, hlast]
      rw [historyRouteFinset_zero_sum]
      simp_rw [hbase]
      change G σL = ∑ e ∈ P, if zσ = e then G σL else 0
      rw [Finset.sum_eq_single zσ]
      · simp
      · intro e he hne
        simp [Ne.symm hne]
      · intro hnot
        exact (hnot hσ).elim
  | succ k ih =>
      intro σL hkσ
      have hklt : k < pathLength S.x := by omega
      let idx := historyRouteIndex (x := S.x) (k + 1)
      let j := pathLength S.x - (k + 1)
      let zσ := (σL.1.1, σL.1.2.1)
      let routeK := historyRouteFinset P k
      let pathFn (γ : EnvPath S.x K) : LogPoint S.x K → ℂ :=
        logHistoryFn F S ρ w (some b) (some γ) distinctWeight k
      let tailFn : LogPoint S.x K → ℂ := fun τ =>
        ∑ γ ∈ routeK, pathFn γ τ
      have hPvToP (τ : LogPoint S.x K)
          (hτ : (τ.1.1, τ.1.2.1) ∈ P) :
          logHistoryFn F S ρ w (some b) none distinctWeight k τ = tailFn τ := by
        exact ih (by omega) τ hτ
      have hcutSum (τ : LogPoint S.x K) :
          logTrunc (some b) (tailFn) τ =
            ∑ γ ∈ routeK, logTrunc (some b) (pathFn γ) τ := by
        exact congrFun (pd_life_b_logTrunc_sum S (some b) routeK pathFn) τ
      have hEdgeFun (τ : LogPoint S.x K)
          (hτ : (τ.1.1, τ.1.2.1) ∈ P) :
          logEdge F S ρ w EdgeKind.full j
              (logTrunc (some b) (logHistoryFn F S ρ w (some b) none distinctWeight k)) τ =
            logEdge F S ρ w EdgeKind.full j (logTrunc (some b) tailFn) τ := by
        have hEq :
            logTrunc (some b) (logHistoryFn F S ρ w (some b) none distinctWeight k) τ =
              logTrunc (some b) tailFn τ := by
          by_cases hcut : memSize τ.1 ≤ b <;>
            simp [logTrunc, hcut, hPvToP τ hτ]
        exact logEdge_full_congr_on_P F S ρ w j P hP
          (logTrunc (some b) (logHistoryFn F S ρ w (some b) none distinctWeight k))
          (logTrunc (some b) tailFn) (fun υ hυ => by
            by_cases hcut : memSize υ.1 ≤ b <;>
              simp [logTrunc, hcut, hPvToP υ hυ]) τ hτ
      let edgeFn (γ : EnvPath S.x K) : LogPoint S.x K → ℂ :=
        fun τ => logEdge F S ρ w EdgeKind.full j (logTrunc (some b) (pathFn γ)) τ
      have hEdgeLin := logEdge_full_sum F S ρ w j routeK
        (fun γ => logTrunc (some b) (pathFn γ)) P hP
      have hEdgeSumAt (τ : LogPoint S.x K)
          (hτ : (τ.1.1, τ.1.2.1) ∈ P) :
          logEdge F S ρ w EdgeKind.full j
              (logTrunc (some b) (logHistoryFn F S ρ w (some b) none distinctWeight k)) τ =
            ∑ γ ∈ routeK, edgeFn γ τ := by
        calc
          _ = logEdge F S ρ w EdgeKind.full j (logTrunc (some b) tailFn) τ := hEdgeFun τ hτ
          _ = _ := by
            have hcutSumFun : logTrunc (some b) tailFn =
                fun υ => ∑ γ ∈ routeK, logTrunc (some b) (pathFn γ) υ := by
              funext υ
              exact hcutSum υ
            exact (congrFun (congrArg (fun f =>
              logEdge F S ρ w EdgeKind.full j f) hcutSumFun) τ).trans (congrFun hEdgeLin τ)
      have hcutEdgeSumAt (τ : LogPoint S.x K)
          (hτ : (τ.1.1, τ.1.2.1) ∈ P) :
          logTrunc (some b)
              (logEdge F S ρ w EdgeKind.full j
                (logTrunc (some b) (logHistoryFn F S ρ w (some b) none distinctWeight k))) τ =
            ∑ γ ∈ routeK, logTrunc (some b) (edgeFn γ) τ := by
        calc
          _ = logTrunc (some b) (fun υ => ∑ γ ∈ routeK, edgeFn γ υ) τ := by
            by_cases hcut : memSize τ.1 ≤ b <;>
              simp [logTrunc, hcut, hEdgeSumAt τ hτ]
          _ = _ := congrFun (pd_life_b_logTrunc_sum S (some b) routeK edgeFn) τ
      have hbadEdge (γ : EnvPath S.x K) :
          ∀ τ, ¬ (τ.2.map Prod.snd).Nodup → logTrunc (some b) (edgeFn γ) τ = 0 := by
        intro τ hbad
        have hfn := pd_life_b_logHistoryFn_zero_of_badLog_nat F S ρ w b
          (some γ) k τ hbad
        have hf : ∀ υ, ¬ (υ.2.map Prod.snd).Nodup →
            logTrunc (some b) (pathFn γ) υ = 0 := by
          intro υ hυ
          have hfn' := pd_life_b_logHistoryFn_zero_of_badLog_nat F S ρ w b
            (some γ) k υ hυ
          by_cases hcut : memSize υ.1 ≤ b
          · simpa [logTrunc, hcut, pathFn] using hfn'
          · simp [logTrunc, hcut, pathFn]
        have hEdgeZero := logEdge_full_zero_of_badLog F S ρ w j
          (logTrunc (some b) (pathFn γ)) hf τ hbad
        simp [logTrunc, edgeFn, hEdgeZero]
      have hghostEdge := logGhost_congr_on_P F S ρ j P
        (fun τ => logTrunc (some b)
          (logEdge F S ρ w EdgeKind.full j
            (logTrunc (some b) (logHistoryFn F S ρ w (some b) none distinctWeight k))) τ)
        (fun τ => ∑ γ ∈ routeK, logTrunc (some b) (edgeFn γ) τ)
        hcutEdgeSumAt σL hkσ
      have hghostLin := logGhost_sum_badLog F S ρ j routeK
        (fun γ => logTrunc (some b) (edgeFn γ)) hbadEdge
      have hghostEdge' :
          logGhost F S ρ j
              (logTrunc (some b)
                (logEdge F S ρ w EdgeKind.full j
                  (logTrunc (some b) (logHistoryFn F S ρ w (some b) none distinctWeight k)))) σL =
            logGhost F S ρ j
              (fun τ => ∑ γ ∈ routeK, logTrunc (some b) (edgeFn γ) τ) σL := by
        change logGhost F S ρ j
          (fun τ => logTrunc (some b)
            (logEdge F S ρ w EdgeKind.full j
              (logTrunc (some b) (logHistoryFn F S ρ w (some b) none distinctWeight k))) τ) σL = _
        exact hghostEdge
      have hleft :
          logHistoryFn F S ρ w (some b) none distinctWeight (k + 1) σL =
            ∑ γ ∈ routeK,
              logTrunc (some b)
                (logGhost F S ρ j (logTrunc (some b) (edgeFn γ))) σL := by
        calc
          _ = logTrunc (some b)
              (logGhost F S ρ j
                (logTrunc (some b)
                  (logEdge F S ρ w EdgeKind.full j
                    (logTrunc (some b) (logHistoryFn F S ρ w (some b) none distinctWeight k)))) ) σL := by
                rfl
          _ = logTrunc (some b)
              (logGhost F S ρ j
                (fun τ => ∑ γ ∈ routeK, logTrunc (some b) (edgeFn γ) τ)) σL := by
                by_cases hcut : memSize σL.1 ≤ b
                · simpa [logTrunc, hcut] using hghostEdge'
                · simp [logTrunc, hcut]
          _ = logTrunc (some b)
              (fun τ => ∑ γ ∈ routeK,
                logGhost F S ρ j (logTrunc (some b) (edgeFn γ)) τ) σL := by
                by_cases hcut : memSize σL.1 ≤ b
                · simp only [logTrunc, hcut]
                  exact congrFun hghostLin σL
                · simp [logTrunc, hcut]
          _ = _ := by
                exact congrFun
                  (pd_life_b_logTrunc_sum S (some b) routeK
                    (fun γ τ => logGhost F S ρ j (logTrunc (some b) (edgeFn γ)) τ)) σL
      have hfixed (γ : EnvPath S.x K) :
          (∑ e ∈ P,
            logHistoryFn F S ρ w (some b)
              (some (Function.update γ idx e)) distinctWeight (k + 1) σL) =
            logTrunc (some b)
              (logGhost F S ρ j (logTrunc (some b) (edgeFn γ))) σL := by
        let G : LogPoint S.x K → ℂ :=
          logGhost F S ρ j (logTrunc (some b) (edgeFn γ))
        have hselector (e : EnvPoint S.x K) :
            logHistoryFn F S ρ w (some b)
                (some (Function.update γ idx e)) distinctWeight (k + 1) σL =
              logTrunc (some b) (fun _ => if zσ = e then G σL else 0) σL := by
          have htail : ∀ t, pathLength S.x - k ≤ t.val →
              Function.update γ idx e t = γ t := by
            intro t ht
            by_cases hti : t = idx
            · subst t
              have hidx : idx.val < pathLength S.x - k := by
                simp [idx, historyRouteIndex]
                omega
              omega
            · simp [Function.update_of_ne hti]
          have hcongr := pd_life_b_logHistoryFn_congrPath_nat F S ρ w b
            distinctWeight k (Function.update γ idx e) γ htail
          have hG :
              logGhost F S ρ j
                (logTrunc (some b)
                  (logEdge F S ρ w EdgeKind.full j
                    (logTrunc (some b)
                      (logHistoryFn F S ρ w (some b)
                        (some (Function.update γ idx e)) distinctWeight k)))) σL = G σL := by
            dsimp [G, edgeFn]
            rw [hcongr]
          calc
            _ = logTrunc (some b)
                  (fun _ => if zσ = e then
                    logGhost F S ρ j
                      (logTrunc (some b)
                        (logEdge F S ρ w EdgeKind.full j
                          (logTrunc (some b)
                            (logHistoryFn F S ρ w (some b)
                              (some (Function.update γ idx e)) distinctWeight k)))) σL
                    else 0) σL := by
                  simp [logHistoryFn, logTrunc, logPathRestrict, idx,
                    historyRouteIndex, Function.update, zσ, j]
            _ = _ := by simp [hG]
        calc
          _ = ∑ e ∈ P, logTrunc (some b) (fun _ => if zσ = e then G σL else 0) σL := by
                apply Finset.sum_congr rfl
                intro e he
                exact hselector e
          _ = logTrunc (some b)
                (fun _ => ∑ e ∈ P, if zσ = e then G σL else 0) σL := by
                symm
                exact congrFun
                  (pd_life_b_logTrunc_sum S (some b) P
                    (fun e _ => if zσ = e then G σL else 0)) σL
          _ = logTrunc (some b) (fun _ => G σL) σL := by
                congr 1
                funext τ
                rw [Finset.sum_eq_single zσ]
                · simp
                · intro e he hne
                  simp [Ne.symm hne]
                · intro hnot
                  exact (hnot hkσ).elim
          _ = logTrunc (some b) G σL := rfl
      rw [hleft]
      rw [historyRouteFinset_succ_sum P k hklt]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro γ hγ
      exact (hfixed γ).symm


private theorem pd_life_b_logGhost_zero_boundary_pos_ne_e1_nat {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (j b : ℕ) (σL : LogPoint S.x K)
    (hpos : σL.1.1 ≠ (1, 0)) :
    logGhost F S ρ j (logTrunc (some b) (logBoundaryOut distinctWeight)) σL = 0 := by
  classical
  unfold logGhost
  apply Finset.sum_eq_zero
  intro D hD
  apply tsum_zero_of_eq_zero
  intro l
  apply Finset.sum_eq_zero
  intro new hnew
  by_cases hDsub : ∀ i, D i ⊆ hitIndices (σL.1.2.2 i) σL.1.1
  · have hboundary :
        logTrunc (some b) (logBoundaryOut distinctWeight)
          (((σL.1.1, σL.1.2.1, fun i =>
            removeIndices (σL.1.2.2 i) (D i) ++
              List.ofFn fun k : Fin (l i) => anchorAt (new i k) σL.1.1),
            σL.2 ++ (List.finRange K).flatMap fun i =>
              List.ofFn fun k : Fin (l i) =>
                (BirthAddress.ghost j i k.val, (new i k : ℕ)))) = 0 := by
      simp [logTrunc, logBoundaryOut, memBoundary, hpos]
    simp [hDsub, hboundary]
  · simp [hDsub]

private theorem pd_life_b_logHistoryFn_zero_of_last_not_e1_nat {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (b : ℕ)
    (γ : EnvPath S.x K) (k : ℕ)
    (hlast : (γ (Fin.last (pathLength S.x))).1 ≠ (1, 0)) :
    logHistoryFn F S ρ w (some b) (some γ) distinctWeight k = fun _ => 0 := by
  induction k with
  | zero =>
      funext σL
      by_cases hmatch : (σL.1.1, σL.1.2.1) = γ (Fin.last (pathLength S.x))
      · have hpos : σL.1.1 ≠ (1, 0) := by
          intro hz
          apply hlast
          exact (congrArg Prod.fst hmatch).symm.trans hz
        have hghost := pd_life_b_logGhost_zero_boundary_pos_ne_e1_nat F S ρ
          (pathLength S.x) b σL hpos
        have hlastIdx :
            (⟨pathLength S.x, Nat.lt_succ_self _⟩ : Fin (pathLength S.x + 1)) =
              Fin.last (pathLength S.x) := by
          apply Fin.ext
          rfl
        have hmatch' : (σL.1.1, σL.1.2.1) =
            γ ⟨pathLength S.x, Nat.lt_succ_self _⟩ := by
          simpa [hlastIdx] using hmatch
        simp [logHistoryFn, logTrunc, logPathRestrict, hmatch', hghost]
      · have hlastIdx :
            (⟨pathLength S.x, Nat.lt_succ_self _⟩ : Fin (pathLength S.x + 1)) =
              Fin.last (pathLength S.x) := by
          apply Fin.ext
          rfl
        have hmatch' : (σL.1.1, σL.1.2.1) ≠
            γ ⟨pathLength S.x, Nat.lt_succ_self _⟩ := by
          simpa [hlastIdx] using hmatch
        simp [logHistoryFn, logTrunc, logPathRestrict, hmatch']
  | succ k ih =>
      funext σL
      have hrec := ih
      have htruncZero : logTrunc (some b) (fun _ => 0 : LogPoint S.x K → ℂ) =
          (fun _ => 0) := by
        funext τ
        simp [logTrunc]
      have hedge : logEdge F S ρ w EdgeKind.full
          (pathLength S.x - (k + 1))
          (logTrunc (some b)
            (logHistoryFn F S ρ w (some b) (some γ) distinctWeight k)) =
            (fun _ => 0) := by
        rw [hrec, htruncZero]
        exact logEdge_full_zero_function F S ρ w _
      have hghost : logGhost F S ρ (pathLength S.x - (k + 1))
          (logTrunc (some b)
            (logEdge F S ρ w EdgeKind.full (pathLength S.x - (k + 1))
              (logTrunc (some b)
                (logHistoryFn F S ρ w (some b) (some γ) distinctWeight k)))) =
            (fun _ => 0) := by
        rw [hrec, htruncZero, logEdge_full_zero_function, htruncZero]
        exact logGhost_zero_function F S ρ _
      simp [logHistoryFn, logTrunc, logPathRestrict, hghost]

private theorem pd_life_b_memHistory_zero_of_last_ne_e1_nat {K : ℕ}
    (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot) (b : ℕ)
    (γ : EnvPath S.x K)
    (hlast : (γ (Fin.last (pathLength S.x))).1 ≠ (1, 0)) :
    memHistory F S ρ w (some b) (some γ) distinctWeight = 0 := by
  classical
  unfold memHistory logInner
  apply tsum_zero_of_eq_zero
  intro σL
  have hfn := pd_life_b_logHistoryFn_zero_of_last_not_e1_nat F S ρ w b γ
    (pathLength S.x) hlast
  rw [congrFun hfn σL]
  simp

private theorem pd_life_b_logHistoryFn_zero_of_path_outside_nat {K : ℕ} (F : PDFix K) (S : PDScale)
    (ρ : ℝ) (w : ArchRoot) (b : ℕ) (P : Finset (EnvPoint S.x K))
    (hP : ∀ t, t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1) (k : ℕ)
    (hk : k ≤ pathLength S.x) :
    ∀ γ : EnvPath S.x K,
      (∃ t, pathLength S.x - k ≤ t.val ∧ γ t ∉ P) →
      ∀ σL, (σL.1.1, σL.1.2.1) ∈ P →
        logHistoryFn F S ρ w (some b) (some γ) distinctWeight k σL = 0 := by
  induction k with
  | zero =>
      intro γ hbad σL hσ
      rcases hbad with ⟨t, ht, hnot⟩
      have htval : t.val = pathLength S.x := by omega
      have htEq : t = Fin.last (pathLength S.x) := by
        apply Fin.ext
        exact htval
      have hlast : γ (Fin.last (pathLength S.x)) ∉ P := by
        simpa [htEq] using hnot
      have hneq : (σL.1.1, σL.1.2.1) ≠ γ (Fin.last (pathLength S.x)) := by
        intro heq
        exact hlast (by simpa [heq] using hσ)
      have hlastIdx :
          (⟨pathLength S.x, Nat.lt_succ_self _⟩ : Fin (pathLength S.x + 1)) =
            Fin.last (pathLength S.x) := by
        apply Fin.ext
        rfl
      have hneq' : (σL.1.1, σL.1.2.1) ≠ γ
          ⟨pathLength S.x, Nat.lt_succ_self _⟩ := by
        simpa [hlastIdx] using hneq
      simp [logHistoryFn, logTrunc, logPathRestrict, hneq']
  | succ k ih =>
      intro γ hbad σL hσ
      have hklt : k < pathLength S.x := by omega
      let idx := historyRouteIndex (x := S.x) (k + 1)
      let j := pathLength S.x - (k + 1)
      have hIdxFin :
          (⟨j, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ : Fin (pathLength S.x + 1)) = idx := by
        apply Fin.ext
        simp [idx, j, historyRouteIndex]
      have hbad' := hbad
      rcases hbad' with ⟨t, ht, hnot⟩
      by_cases hcur : (σL.1.1, σL.1.2.1) = γ idx
      · have hcurP : γ idx ∈ P := by simpa [hcur] using hσ
        have hti : t ≠ idx := by
          intro heq
          subst t
          exact hnot hcurP
        have htTail : pathLength S.x - k ≤ t.val := by
          have hneVal : t.val ≠ idx.val := by
            intro heq
            apply hti
            exact Fin.ext heq
          change idx.val ≤ t.val at ht
          have hltVal : idx.val < t.val := lt_of_le_of_ne ht (Ne.symm hneVal)
          have hidxplus : idx.val + 1 = pathLength S.x - k := by
            simp [idx, historyRouteIndex]
            omega
          omega
        have hbadTail : ∃ t, pathLength S.x - k ≤ t.val ∧ γ t ∉ P :=
          ⟨t, htTail, hnot⟩
        have hrecZero (τ : LogPoint S.x K)
            (hτ : (τ.1.1, τ.1.2.1) ∈ P) :
            logHistoryFn F S ρ w (some b) (some γ) distinctWeight k τ = 0 :=
          ih (by omega) γ hbadTail τ hτ
        have hEdgeZero (τ : LogPoint S.x K)
            (hτ : (τ.1.1, τ.1.2.1) ∈ P) :
            logEdge F S ρ w EdgeKind.full j
                (logTrunc (some b)
                  (logHistoryFn F S ρ w (some b) (some γ) distinctWeight k)) τ = 0 := by
          rw [logEdge_full_congr_on_P F S ρ w j P hP
            (logTrunc (some b) (logHistoryFn F S ρ w (some b) (some γ) distinctWeight k))
            (fun _ => 0)
            (by
              intro υ hυ
              have hrec := hrecZero υ hυ
              by_cases hcut : memSize υ.1 ≤ b <;> simp [logTrunc, hcut, hrec]) τ hτ]
          exact congrFun (logEdge_full_zero_function F S ρ w j) τ
        have hEdgeTruncZero (τ : LogPoint S.x K)
            (hτ : (τ.1.1, τ.1.2.1) ∈ P) :
            logTrunc (some b)
              (logEdge F S ρ w EdgeKind.full j
                (logTrunc (some b) (logHistoryFn F S ρ w (some b) (some γ) distinctWeight k))) τ = 0 := by
          have he := hEdgeZero τ hτ
          by_cases hcut : memSize τ.1 ≤ b <;> simp [logTrunc, hcut, he]
        have hghostZero := logGhost_congr_on_P F S ρ j P
          (fun τ => logTrunc (some b)
            (logEdge F S ρ w EdgeKind.full j
              (logTrunc (some b) (logHistoryFn F S ρ w (some b) (some γ) distinctWeight k))) τ)
          (fun _ => 0) hEdgeTruncZero σL hσ
        have hfinalWrapped :
            logGhost F S ρ j
              (logTrunc (some b)
                (logEdge F S ρ w EdgeKind.full j
                  (logTrunc (some b)
                    (logHistoryFn F S ρ w (some b) (some γ) distinctWeight k)))) σL = 0 :=
          hghostZero.trans (congrFun (logGhost_zero_function F S ρ j) σL)
        have hcurrent : (σL.1.1, σL.1.2.1) = γ
            ⟨j, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
          simpa [hIdxFin] using hcur
        by_cases hcut : memSize σL.1 ≤ b
        · simpa [logHistoryFn, logTrunc, logPathRestrict, j, hcurrent, hcut] using hfinalWrapped
        · simp [logHistoryFn, logTrunc, logPathRestrict, j, hcurrent, hcut]
      · have hcur' : (σL.1.1, σL.1.2.1) ≠ γ
            ⟨j, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
          simpa [hIdxFin] using hcur
        simp [logHistoryFn, logTrunc, logPathRestrict, j, hcur']



theorem pd_life_b_history_paths_trunc (δ c₁ c₂ : ℝ) (b : ℕ)
    {K : ℕ} (F : PDFix K) (S : PDScale) (ρ : ℝ) (w : ArchRoot)
    (hS : S.Valid K δ c₁ c₂) (hw : w.InRegion S) :
    memHistory F S ρ w (some b) none distinctWeight =
      ∑' γ : EnvPath S.x K,
        if IsEnvPathAdmissible F S γ then
          memHistory F S ρ w (some b) (some γ) distinctWeight else 0 := by
  classical
  rcases hS with ⟨hxS, hHm, hHn, _, _, hY, hpad⟩
  have hxpos : 0 < S.x := by linarith
  have hpowpos : 0 < Real.rpow S.x δ := Real.rpow_pos_of_pos hxpos _
  have hHmpos : 0 < S.Hm := lt_of_lt_of_le hpowpos hHm
  have hHnpos : 0 < S.Hn := lt_of_lt_of_le hpowpos hHn
  have hYpos : 0 < S.Y := by
    unfold dyadicScales at hY
    rcases Finset.mem_filter.mp hY with ⟨himage, _⟩
    rcases Finset.mem_image.mp himage with ⟨n, _, hEq⟩
    rw [← hEq]
    positivity
  have hd0pos : 0 < (S.d₀ : ℝ) := by
    unfold padScales at hpad
    rcases Finset.mem_image.mp hpad with ⟨n, _, hEq⟩
    rw [← hEq]
    positivity
  have hUpos : 0 < S.U := by
    dsimp [PDScale.U, PDScale.H]
    exact mul_pos (mul_pos hd0pos hYpos) hHmpos
  have hVpos : 0 < S.V := by
    simpa [PDScale.V] using hHnpos
  have hlogpos : 0 < Real.log S.x := Real.log_pos (by linarith [hxS])
  let rArg := Real.rpow (Real.log S.x) (1 / 2 : ℝ) / 2
  have hrArg : 0 < rArg := by
    dsimp [rArg]
    exact div_pos (Real.rpow_pos_of_pos hlogpos _) (by norm_num)
  have hRpos : 0 < momentR S.x := by
    change 0 < ⌈rArg⌉₊
    by_contra hR
    have hRzero : (⌈rArg⌉₊ : ℕ) = 0 := by omega
    have hceil : rArg ≤ (⌈rArg⌉₊ : ℕ) := Nat.le_ceil rArg
    rw [hRzero] at hceil
    have hceil' : rArg ≤ 0 := by exact_mod_cast hceil
    exact (not_le_of_gt hrArg) hceil'
  have hNpos : 0 < pathLength S.x := by
    dsimp [pathLength]
    exact Nat.mul_pos (by omega) hRpos
  have hwRegion := hw
  rcases hw with ⟨hu1, hu2, hv1, hv2, _, _⟩
  have he1box : envBox S w (1, 0) := by
    simpa [envBox, ArchRoot.tau] using ⟨hu1, hu2, hv1, hv2⟩
  have hPfin := envPoint_valid_box_finite F S w hUpos hVpos hwRegion
  let P : Finset (EnvPoint S.x K) := hPfin.toFinset
  have hP (t : EnvPoint S.x K) :
      t ∈ P ↔ EnvValid F S t ∧ envBox S w t.1 := by
    simp [P]
  let R : Finset (EnvPath S.x K) := historyRouteFinset P (pathLength S.x)
  let T : Finset (LogPoint S.x K) := historyInitialLogs F.a
  let coeff (σL : LogPoint S.x K) : ℂ :=
    (memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL)
  have hInitFacts (σL : LogPoint S.x K)
      (hμ : memMeasure F S σL.1 ≠ 0) (hb : logBoundaryIn σL ≠ 0) :
      σL ∈ T ∧ MemValid F S σL.1 ∧
        σL.1.1 = (1, 0) ∧ (∀ i, σL.1.2.2 i = []) ∧
        σL.2 = initialLog σL.1 := by
    have hlog : σL.2 = initialLog σL.1 := by
      by_contra hn
      apply hb
      simp [logBoundaryIn, hn]
    have hboundary : σL.1.1 = (1, 0) ∧ (∀ i, σL.1.2.2 i = []) := by
      by_contra hn
      apply hb
      simp [logBoundaryIn, hlog, memBoundary, hn]
    have hvalid : MemValid F S σL.1 := by
      by_contra hn
      apply hμ
      simp [memMeasure, hn]
    have hmemT : σL ∈ T := by
      apply (mem_historyInitialLogs F.a σL).2
      exact ⟨hboundary.1, hboundary.2, hlog, hvalid.2.1⟩
    exact ⟨hmemT, hvalid, hboundary.1, hboundary.2, hlog⟩
  have hcoeffzero : ∀ σL, σL ∉ T → coeff σL = 0 := by
    intro σL hσ
    by_cases hμ : memMeasure F S σL.1 = 0
    · simp [coeff, hμ]
    · by_cases hb : logBoundaryIn σL = 0
      · simp [coeff, hb]
      · exact (hσ (hInitFacts σL hμ hb).1).elim
  have hroutePoint (σL : LogPoint S.x K) :
      coeff σL * logHistoryFn F S ρ w (some b) none distinctWeight (pathLength S.x) σL =
        ∑ γ ∈ R, coeff σL *
          logHistoryFn F S ρ w (some b) (some γ) distinctWeight (pathLength S.x) σL := by
    by_cases hμ : memMeasure F S σL.1 = 0
    · simp [coeff, hμ]
    · by_cases hb : logBoundaryIn σL = 0
      · simp [coeff, hb]
      · obtain ⟨hT, hvalid, hz, hmem, hlog⟩ := hInitFacts σL hμ hb
        by_cases hnd : (σL.2.map Prod.snd).Nodup
        · have hndInit : ((initialLog σL.1).map Prod.snd).Nodup := by
            simpa [hlog] using hnd
          have hband : ∀ i j, σL.1.2.1 i j ∈ primeBand S.x (F.a i) := hvalid.2.1
          have hLists := initialLog_nodup_validLists F.a σL.1 hband hndInit
          have hEnv : EnvValid F S (σL.1.1, σL.1.2.1) := by
            refine ⟨?_, hLists⟩
            norm_num [hz, Int.gcd]
          have hsource : (σL.1.1, σL.1.2.1) ∈ P :=
            (hP _).2 ⟨hEnv, by simpa [hz] using he1box⟩
          have hroute := pd_life_b_logHistoryFn_route_sum_nat F S ρ w b P hP
            (pathLength S.x) le_rfl σL hsource
          calc
            _ = coeff σL *
                (∑ γ ∈ R,
                  logHistoryFn F S ρ w (some b) (some γ) distinctWeight
                    (pathLength S.x) σL) := congrArg (fun z => coeff σL * z) hroute
            _ = _ := by rw [Finset.mul_sum]
        · have hzeroNone :=
            pd_life_b_logHistoryFn_zero_of_badLog_nat F S ρ w b none (pathLength S.x) σL hnd
          have hzeroPath (γ : EnvPath S.x K) :=
            pd_life_b_logHistoryFn_zero_of_badLog_nat F S ρ w b (some γ) (pathLength S.x) σL hnd
          simp [hzeroNone, hzeroPath]
  have hfiniteDecomp :
      memHistory F S ρ w (some b) none distinctWeight =
        ∑ γ ∈ R, memHistory F S ρ w (some b) (some γ) distinctWeight := by
    unfold memHistory logInner
    change (∑' σL, coeff σL *
          logHistoryFn F S ρ w (some b) none distinctWeight (pathLength S.x) σL) = _
    calc
      _ = ∑' σL, ∑ γ ∈ R, coeff σL *
            logHistoryFn F S ρ w (some b) (some γ) distinctWeight (pathLength S.x) σL := by
          apply tsum_congr
          intro σL
          exact hroutePoint σL
      _ = ∑ γ ∈ R, ∑' σL, coeff σL *
            logHistoryFn F S ρ w (some b) (some γ) distinctWeight (pathLength S.x) σL :=
          tsum_sum_finite_support T R
            (fun σL γ => coeff σL *
              logHistoryFn F S ρ w (some b) (some γ) distinctWeight (pathLength S.x) σL)
            (by
              intro γ σL hσ
              simp [hcoeffzero σL hσ])
      _ = _ := rfl
  have hbadOutside (γ : EnvPath S.x K) (hγ : γ ∉ R) :
      ∃ t, pathLength S.x - pathLength S.x ≤ t.val ∧ γ t ∉ P := by
    by_contra hn
    have hall : ∀ t, γ t ∈ P := by
      intro t
      by_contra hnot
      exact hn ⟨t, by omega, hnot⟩
    have hroute : γ ∈ historyRouteFinset P (pathLength S.x) := by
      rw [mem_historyRouteFinset]
      constructor
      · intro t ht
        exact hall t
      · intro t ht
        have ht0 : t.val < 0 := by simpa using ht
        omega
    exact hγ (by simpa [R] using hroute)
  have hmemZeroOutside (γ : EnvPath S.x K) (hγ : γ ∉ R) :
      memHistory F S ρ w (some b) (some γ) distinctWeight = 0 := by
    have hbad := hbadOutside γ hγ
    unfold memHistory logInner
    apply tsum_zero_of_eq_zero
    intro σL
    by_cases hT : σL ∈ T
    · rcases (mem_historyInitialLogs F.a σL).mp hT with ⟨hz, hmem, hlog, hband⟩
      by_cases hnd : (σL.2.map Prod.snd).Nodup
      · have hndInit : ((initialLog σL.1).map Prod.snd).Nodup := by
          simpa [hlog] using hnd
        have hLists := initialLog_nodup_validLists F.a σL.1 hband hndInit
        have hEnv : EnvValid F S (σL.1.1, σL.1.2.1) := by
          refine ⟨?_, hLists⟩
          norm_num [hz, Int.gcd]
        have hsource : (σL.1.1, σL.1.2.1) ∈ P :=
          (hP _).2 ⟨hEnv, by simpa [hz] using he1box⟩
        have hzero := pd_life_b_logHistoryFn_zero_of_path_outside_nat F S ρ w b P hP
          (pathLength S.x) le_rfl γ hbad σL hsource
        change coeff σL *
          logHistoryFn F S ρ w (some b) (some γ) distinctWeight (pathLength S.x) σL = 0
        rw [hzero]
        simp
      · have hzero :=
          pd_life_b_logHistoryFn_zero_of_badLog_nat F S ρ w b (some γ) (pathLength S.x) σL hnd
        change coeff σL *
          logHistoryFn F S ρ w (some b) (some γ) distinctWeight (pathLength S.x) σL = 0
        rw [hzero]
        simp
    · have hc :
          (memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL) = 0 := by
        simpa [coeff] using hcoeffzero σL hT
      change ((memMeasure F S σL.1 : ℂ) * star (logBoundaryIn σL)) *
        logHistoryFn F S ρ w (some b) (some γ) distinctWeight (pathLength S.x) σL = 0
      rw [hc]
      simp
  have hrestrictedZeroNonAdm (γ : EnvPath S.x K) (hγ : γ ∈ R)
      (hAdm : ¬ IsEnvPathAdmissible F S γ) :
      memHistory F S ρ w (some b) (some γ) distinctWeight = 0 := by
    have hroute := (mem_historyRouteFinset P (pathLength S.x) γ).mp
      (by simpa [R] using hγ)
    have hvalidAll : ∀ j, EnvValid F S (γ j) := by
      intro j
      have hj : pathLength S.x - pathLength S.x ≤ j.val := by omega
      exact (hP (γ j)).mp (hroute.1 j hj) |>.1
    by_cases hstart : (γ ⟨0, Nat.zero_lt_succ (pathLength S.x)⟩).1 = (1, 0)
    · by_cases hlast : (γ (Fin.last (pathLength S.x))).1 = (1, 0)
      · exact (hAdm ⟨hvalidAll, by simpa using hstart, hlast⟩).elim
      · exact pd_life_b_memHistory_zero_of_last_ne_e1_nat F S ρ w b γ hlast
    · have hstart' : (γ 0).1 ≠ (1, 0) := by simpa using hstart
      exact pd_life_b_memHistory_zero_of_start_ne_e1 F S ρ w (some b) γ
        distinctWeight hstart'
  have hsumAdm :
      (∑ γ ∈ R, memHistory F S ρ w (some b) (some γ) distinctWeight) =
        ∑ γ ∈ R,
          if IsEnvPathAdmissible F S γ then
            memHistory F S ρ w (some b) (some γ) distinctWeight else 0 := by
    apply Finset.sum_congr rfl
    intro γ hγ
    by_cases hAdm : IsEnvPathAdmissible F S γ
    · simp [hAdm]
    · simp [hAdm, hrestrictedZeroNonAdm γ hγ hAdm]
  have htsumAll :
      (∑' γ : EnvPath S.x K,
        if IsEnvPathAdmissible F S γ then
          memHistory F S ρ w (some b) (some γ) distinctWeight else 0) =
        ∑ γ ∈ R,
          if IsEnvPathAdmissible F S γ then
            memHistory F S ρ w (some b) (some γ) distinctWeight else 0 := by
    apply tsum_eq_sum
    intro γ hγ
    by_cases hAdm : IsEnvPathAdmissible F S γ
    · simp [hAdm, hmemZeroOutside γ hγ]
    · simp [hAdm]
  calc
    memHistory F S ρ w (some b) none distinctWeight =
        ∑ γ ∈ R, memHistory F S ρ w (some b) (some γ) distinctWeight := hfiniteDecomp
    _ = ∑ γ ∈ R,
          if IsEnvPathAdmissible F S γ then
            memHistory F S ρ w (some b) (some γ) distinctWeight else 0 := hsumAdm
    _ = _ := htsumAll.symm



set_option maxHeartbeats 5000000 in
theorem pd_life_b_doubled_assignment_sum {K : ℕ} (F : PDFix K)
    (S : PDScale) (γ : EnvPath S.x K) :
    (∑ H : PDLifeAssignment F S γ,
      (2 : ℝ) ^ pdLifeGhostBirths F S γ H * |pdLifeAssignmentCharge F S γ H|) =
      doubledLifeMajorant F S γ := by
  classical
  let q (i : Fin K) (p : primeBand S.x (F.a i)) (life : PrimeLife S γ p.1) : ℝ :=
    (if life.1.1.isSome then 2 else 1) * |primeLifeCharge F S γ p.1 life|
  have hGhost (H : PDLifeAssignment F S γ) :
      (2 : ℝ) ^ pdLifeGhostBirths F S γ H =
        ∏ i : Fin K, ∏ p : primeBand S.x (F.a i),
          (if (H i p).1.1.isSome then 2 else 1) := by
    unfold pdLifeGhostBirths
    calc
      _ = ∏ i : Fin K, (2 : ℝ) ^
          ∑ p : primeBand S.x (F.a i), if (H i p).1.1.isSome then 1 else 0 := by
            symm
            simpa using (Finset.prod_pow_eq_pow_sum Finset.univ
              (fun i : Fin K => ∑ p : primeBand S.x (F.a i),
                if (H i p).1.1.isSome then 1 else 0) (2 : ℝ))
      _ = ∏ i : Fin K, ∏ p : primeBand S.x (F.a i),
          (2 : ℝ) ^ (if (H i p).1.1.isSome then 1 else 0) := by
            apply Finset.prod_congr rfl
            intro i hi
            symm
            simpa using (Finset.prod_pow_eq_pow_sum Finset.univ
              (fun p : primeBand S.x (F.a i) => if (H i p).1.1.isSome then 1 else 0)
              (2 : ℝ))
      _ = ∏ i : Fin K, ∏ p : primeBand S.x (F.a i),
          (if (H i p).1.1.isSome then 2 else 1) := by
            apply Finset.prod_congr rfl
            intro i hi
            apply Finset.prod_congr rfl
            intro p hp
            split_ifs <;> norm_num
  have hCharge (H : PDLifeAssignment F S γ) :
      (2 : ℝ) ^ pdLifeGhostBirths F S γ H * |pdLifeAssignmentCharge F S γ H| =
        ∏ i : Fin K, ∏ p : primeBand S.x (F.a i), q i p (H i p) := by
    rw [hGhost H]
    simp only [pdLifeAssignmentCharge, Finset.abs_prod, Finset.prod_attach]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [← Finset.prod_mul_distrib]
  calc
    _ = ∑ H : PDLifeAssignment F S γ,
          ∏ i : Fin K, ∏ p : primeBand S.x (F.a i), q i p (H i p) := by
        apply Finset.sum_congr rfl
        intro H hH
        exact hCharge H
    _ = ∏ i : Fin K,
          ∑ g : (p : primeBand S.x (F.a i)) → PrimeLife S γ p.1,
            ∏ p : primeBand S.x (F.a i), q i p (g p) := by
        symm
        simpa only [PDLifeAssignment] using
          (Fintype.prod_sum (fun (i : Fin K)
              (g : (p : primeBand S.x (F.a i)) → PrimeLife S γ p.1) =>
            ∏ p : primeBand S.x (F.a i), q i p (g p)))
    _ = ∏ i : Fin K, ∏ p : primeBand S.x (F.a i),
          ∑ life : PrimeLife S γ p.1, q i p life := by
        apply Finset.prod_congr rfl
        intro i hi
        symm
        exact Fintype.prod_sum (fun (p : primeBand S.x (F.a i))
          (life : PrimeLife S γ p.1) => q i p life)
    _ = doubledLifeMajorant F S γ := by
        simp [doubledLifeMajorant, q]


end
end ArtinPrimitiveRoots.Proofs.pd_life_b
