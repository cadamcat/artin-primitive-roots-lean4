import ArtinPrimitiveRoots.Sieve.Block.Transfer

namespace ArtinPrimitiveRoots.Sieve.Block

open Finset

/-- The natural-number embedding of the finite subtype determined by a prime set. -/
def subtypeValEmbedding (P : Finset ℕ) : ↥P ↪ ℕ :=
  ⟨Subtype.val, fun a b hab => Subtype.ext hab⟩

theorem subtypeVal_map_univ (P : Finset ℕ) :
    (Finset.univ : Finset ↥P).map (subtypeValEmbedding P) = P := by
  classical
  ext n
  constructor
  · intro hn
    rcases Finset.mem_map.mp hn with ⟨p, hp, hpn⟩
    subst n
    exact p.2
  · intro hn
    let p : ↥P := ⟨n, hn⟩
    exact Finset.mem_map.mpr ⟨p, Finset.mem_univ p, rfl⟩

/-- Mapping the preimage of a subset of `P` back into the subtype recovers that subset. -/
theorem map_preimage_subtype_eq {P D : Finset ℕ} (hD : D ⊆ P) :
    (D.preimage (subtypeValEmbedding P)
      (subtypeValEmbedding P).injective.injOn).map (subtypeValEmbedding P) = D := by
  classical
  ext n
  constructor
  · intro hn
    rcases Finset.mem_map.mp hn with ⟨p, hp, hpn⟩
    subst n
    exact Finset.mem_preimage.mp hp
  · intro hn
    let p : ↥P := ⟨n, hD hn⟩
    exact Finset.mem_map.mpr ⟨p, Finset.mem_preimage.mpr hn, rfl⟩

/-- Intersections commute with mapping the finite subtype into the natural numbers. -/
theorem weightedIntersection_map_subtype {α : Type*} [DecidableEq ℕ]
    (A : Finset α) (wt : α → ℝ) (P : Finset ℕ)
    (bad : ℕ → α → Prop) (D : Finset ↥P) :
    weightedIntersection A wt (fun p : ↥P => bad p.1) D =
      weightedIntersection A wt bad (D.map (subtypeValEmbedding P)) := by
  classical
  unfold weightedIntersection
  have hiff (a : α) :
      (∀ p ∈ D, bad p.1 a) ↔
        ∀ q ∈ D.map (subtypeValEmbedding P), bad q a := by
    constructor
    · intro h q hq
      rcases Finset.mem_map.mp hq with ⟨p, hp, rfl⟩
      exact h p hp
    · intro h p hp
      exact h p.1 (Finset.mem_map.mpr ⟨p, hp, rfl⟩)
  let leftExpanded : α → Prop := fun a =>
    ∀ n (hn : n ∈ P), (⟨n, hn⟩ : ↥P) ∈ D → bad n a
  let rightExpanded : α → Prop := fun a =>
    ∀ p (n : ℕ) (hn : n ∈ P), (⟨n, hn⟩ : ↥P) ∈ D →
      subtypeValEmbedding P ⟨n, hn⟩ = p → bad p a
  have hleftExpanded (a : α) :
      leftExpanded a ↔ ∀ p ∈ D, bad p.1 a := by
    constructor
    · intro h p hp
      exact h p.1 p.2 hp
    · intro h n hn hp
      exact h ⟨n, hn⟩ hp
  have hrightExpanded (a : α) :
      rightExpanded a ↔ ∀ q ∈ D.map (subtypeValEmbedding P), bad q a := by
    constructor
    · intro h q hq
      rcases Finset.mem_map.mp hq with ⟨p, hp, hpq⟩
      exact h q p.1 p.2 hp hpq
    · intro h p n hn hp hpn
      exact h p (Finset.mem_map.mpr ⟨⟨n, hn⟩, hp, hpn⟩)
  have hiffExpanded (a : α) : leftExpanded a ↔ rightExpanded a :=
    (hleftExpanded a).trans ((hiff a).trans (hrightExpanded a).symm)
  rw [Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a ha
  have hterm :
      (if leftExpanded a then wt a else 0) =
        (if rightExpanded a then wt a else 0) := by
    by_cases hp : leftExpanded a
    · have hq := (hiffExpanded a).mp hp
      simp [hp, hq]
    · have hq : ¬ rightExpanded a := fun hq => hp ((hiffExpanded a).mpr hq)
      simp [hp, hq]
  simpa [leftExpanded, rightExpanded] using hterm

/-- The model error over a subtype subset agrees with the frozen error on its natural image. -/
theorem subtypeError_eq_map {α : Type*} [DecidableEq ℕ]
    (A : Finset α) (wt : α → ℝ) (P : Finset ℕ)
    (bad : ℕ → α → Prop) (X : ℝ) (g : ℕ → ℝ) (D : Finset ↥P) :
    (weightedIntersection A wt (fun p : ↥P => bad p.1) D -
        X * ∏ p ∈ D, g p.1) =
      (weightedIntersection A wt bad (D.map (subtypeValEmbedding P)) -
        X * ∏ p ∈ D.map (subtypeValEmbedding P), g p) := by
  rw [weightedIntersection_map_subtype]
  have hprod : (∏ p ∈ D, g p.1) =
      ∏ p ∈ D.map (subtypeValEmbedding P), g p := by
    exact (Finset.prod_map D (subtypeValEmbedding P) g).symm
  rw [hprod]

/-- Reindex an error sum on subtype subsets by their natural-number images. -/
theorem sum_subtype_support_errors_eq {α : Type*} [DecidableEq ℕ]
    (P : Finset ℕ) (Q : Finset (Finset ℕ)) (hQ : Q ⊆ P.powerset)
    (Esub : Finset ↥P → ℝ) (Enat : Finset ℕ → ℝ)
    (hE : ∀ D : Finset ↥P,
      Esub D = Enat (D.map (subtypeValEmbedding P))) :
    (∑ D ∈ Q.preimage
        (fun D : Finset ↥P => D.map (subtypeValEmbedding P))
        (Finset.map_injective (subtypeValEmbedding P)).injOn, |Esub D|) =
      ∑ D ∈ Q, |Enat D| := by
  classical
  let e := subtypeValEmbedding P
  let f : Finset ↥P → Finset ℕ := fun D => D.map e
  let Qsub := Q.preimage f (Finset.map_injective e).injOn
  change (∑ D ∈ Qsub, |Esub D|) = ∑ D ∈ Q, |Enat D|
  apply Finset.sum_bij (fun D _ => f D)
  · intro D hD
    exact Finset.mem_preimage.mp hD
  · intro D hD D' hD' hmap
    exact (Finset.map_injective e) hmap
  · intro D hD
    have hDsub : D ⊆ P := Finset.mem_powerset.mp (hQ hD)
    let Dsub := D.preimage e e.injective.injOn
    have hmap : Dsub.map e = D := map_preimage_subtype_eq hDsub
    refine ⟨Dsub, ?_, hmap⟩
    exact Finset.mem_preimage.mpr (by simpa [f, hmap] using hD)
  · intro D hD
    rw [hE]

end ArtinPrimitiveRoots.Sieve.Block
