import ArtinPrimitiveRoots.A1.Coefficients

set_option autoImplicit false
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_euler_sol.e_b
open ArtinPrimitiveRoots A1
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)} (S : SData F CE condη)

abbrev OutsidePrime := {v : FinPlace F // v ∉ S.Sf}
abbrev Tuple := S.SqfExtIdeal × S.ExtIdeal × S.ExtIdeal × S.ExtIdeal
abbrev PrimeIndex := Fin 2 × ℕ × ℕ × ℕ

def idealEmbedding : OutsidePrime S ↪ Ideal (𝓞 F) where
  toFun v := v.1.asIdeal
  inj' _ _ h := Subtype.ext (HeightOneSpectrum.ext h)

def factors (I : S.ExtIdeal) : OutsidePrime S →₀ ℕ :=
  Finsupp.comapDomain (idealEmbedding S)
    (UniqueFactorizationMonoid.normalizedFactors I.1).toFinsupp
    (idealEmbedding S).injective.injOn

theorem factors_apply (I : S.ExtIdeal) (v : OutsidePrime S) :
    factors S I v = (UniqueFactorizationMonoid.normalizedFactors I.1).count v.1.asIdeal := rfl

theorem factor_exterior (I : S.ExtIdeal) (P : Ideal (𝓞 F))
    (hP : P ∈ UniqueFactorizationMonoid.normalizedFactors I.1) :
    ∃ v : OutsidePrime S, v.1.asIdeal = P := by
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  let v : FinPlace F := ⟨P, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
  refine ⟨⟨v, ?_⟩, rfl⟩
  intro hv
  exact I.2.2 v hv (Ideal.dvd_iff_le.mp
    (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP))

theorem factors_injective : Function.Injective (factors S) := by
  intro I J hIJ
  apply Subtype.ext
  have hnf : UniqueFactorizationMonoid.normalizedFactors I.1 =
      UniqueFactorizationMonoid.normalizedFactors J.1 := by
    apply Multiset.ext.mpr
    intro P
    by_cases hI : P ∈ UniqueFactorizationMonoid.normalizedFactors I.1
    · obtain ⟨v, hv⟩ := factor_exterior S I P hI
      simpa only [factors_apply, hv] using congrArg (fun f => f v) hIJ
    · by_cases hJ : P ∈ UniqueFactorizationMonoid.normalizedFactors J.1
      · obtain ⟨v, hv⟩ := factor_exterior S J P hJ
        simpa only [factors_apply, hv] using congrArg (fun f => f v) hIJ
      · simp [Multiset.count_eq_zero.mpr hI, Multiset.count_eq_zero.mpr hJ]
  rw [← Ideal.prod_normalizedFactors_eq_self I.2.1,
    ← Ideal.prod_normalizedFactors_eq_self J.2.1, hnf]

theorem prime_product_exterior (m : Multiset (OutsidePrime S)) :
    S.IsExterior (m.map (idealEmbedding S)).prod := by
  induction m using Multiset.induction_on with
  | empty =>
      refine ⟨by simp, ?_⟩
      intro v hv hle
      have htop : (⊤ : Ideal (𝓞 F)) ≤ v.asIdeal := by simpa using hle
      exact v.isPrime.ne_top (top_le_iff.mp htop)
  | @cons p m ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      refine ⟨mul_ne_zero p.1.ne_bot ih.1, ?_⟩
      intro v hv hle
      rcases v.prime.dvd_mul.mp (Ideal.dvd_iff_le.mpr hle) with hp | hm
      · have heq : p.1 = v := HeightOneSpectrum.ext
          (p.1.isMaximal.eq_of_le v.isPrime.ne_top (Ideal.dvd_iff_le.mp hp))
        exact p.2 (heq.symm ▸ hv)
      · exact ih.2 v hv (Ideal.dvd_iff_le.mp hm)

def fromFactors (f : OutsidePrime S →₀ ℕ) : S.ExtIdeal :=
  ⟨(f.toMultiset.map (idealEmbedding S)).prod, prime_product_exterior S f.toMultiset⟩

theorem normalizedFactors_fromFactors (f : OutsidePrime S →₀ ℕ) :
    UniqueFactorizationMonoid.normalizedFactors (fromFactors S f).1 =
      f.toMultiset.map (idealEmbedding S) := by
  apply UniqueFactorizationMonoid.normalizedFactors_prod_of_prime
  intro P hP
  obtain ⟨v, hv, rfl⟩ := Multiset.mem_map.mp hP
  exact v.1.prime

theorem factors_fromFactors (f : OutsidePrime S →₀ ℕ) : factors S (fromFactors S f) = f := by
  ext v
  rw [factors_apply, normalizedFactors_fromFactors]
  change (f.toMultiset.map (idealEmbedding S)).count (idealEmbedding S v) = f v
  rw [Multiset.count_map_eq_count' _ _ (idealEmbedding S).injective,
    Finsupp.count_toMultiset]

def extEquiv : S.ExtIdeal ≃ (OutsidePrime S →₀ ℕ) where
  toFun := factors S
  invFun := fromFactors S
  left_inv I := factors_injective S (factors_fromFactors S (factors S I))
  right_inv := factors_fromFactors S

theorem squarefree_count_lt (c : S.SqfExtIdeal) (v : OutsidePrime S) :
    factors S ⟨c.1, c.2.1⟩ v < 2 := by
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors c.2.1.1).mp c.2.2
  have hle := Multiset.nodup_iff_count_le_one.mp hnodup v.1.asIdeal
  change (UniqueFactorizationMonoid.normalizedFactors c.1).count v.1.asIdeal < 2
  omega

def sqfFactors (c : S.SqfExtIdeal) : OutsidePrime S →₀ Fin 2 :=
  (factors S ⟨c.1, c.2.1⟩).mapRange (fun n : ℕ => Fin.ofNat 2 n) (by rfl)

theorem sqfFactors_val (c : S.SqfExtIdeal) (v : OutsidePrime S) :
    (sqfFactors S c v).val =
      (UniqueFactorizationMonoid.normalizedFactors c.1).count v.1.asIdeal := by
  change (factors S ⟨c.1, c.2.1⟩ v) % 2 = _
  rw [Nat.mod_eq_of_lt (squarefree_count_lt S c v)]
  rfl

def fromSqfFactors (f : OutsidePrime S →₀ Fin 2) : S.SqfExtIdeal :=
  let g := f.mapRange Fin.val rfl
  let I := fromFactors S g
  ⟨I.1, I.2, by
    apply (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors I.2.1).mpr
    rw [normalizedFactors_fromFactors]
    apply Multiset.Nodup.map (idealEmbedding S).injective
    apply Multiset.nodup_iff_count_le_one.mpr
    intro v
    rw [Finsupp.count_toMultiset]
    change (f v).val ≤ 1
    have hv := (f v).isLt
    omega⟩

theorem sqfFactors_fromSqfFactors (f : OutsidePrime S →₀ Fin 2) :
    sqfFactors S (fromSqfFactors S f) = f := by
  apply Finsupp.ext
  intro v
  apply Fin.ext
  rw [sqfFactors_val]
  change (UniqueFactorizationMonoid.normalizedFactors
    (fromFactors S (f.mapRange Fin.val rfl)).1).count v.1.asIdeal = (f v).val
  rw [← factors_apply, factors_fromFactors]
  rfl

def sqfEquiv : S.SqfExtIdeal ≃ (OutsidePrime S →₀ Fin 2) where
  toFun := sqfFactors S
  invFun := fromSqfFactors S
  left_inv c := by
    apply Subtype.ext
    have h : (⟨(fromSqfFactors S (sqfFactors S c)).1,
        (fromSqfFactors S (sqfFactors S c)).2.1⟩ : S.ExtIdeal) = ⟨c.1, c.2.1⟩ := by
      apply factors_injective S
      apply Finsupp.ext
      intro v
      have heq := congrArg (fun f => (f v).val) (sqfFactors_fromSqfFactors S (sqfFactors S c))
      change (UniqueFactorizationMonoid.normalizedFactors
        (fromSqfFactors S (sqfFactors S c)).1).count v.1.asIdeal =
          (UniqueFactorizationMonoid.normalizedFactors c.1).count v.1.asIdeal
      simpa only [sqfFactors_val] using heq
    exact congrArg (fun I : S.ExtIdeal => I.1) h
  right_inv := sqfFactors_fromSqfFactors S

def zipEquiv {α β γ : Type*} [Zero β] [Zero γ] :
    ((α →₀ β) × (α →₀ γ)) ≃ (α →₀ β × γ) where
  toFun p := Finsupp.zipWith Prod.mk rfl p.1 p.2
  invFun f := (f.mapRange Prod.fst rfl, f.mapRange Prod.snd rfl)
  left_inv p := by
    apply Prod.ext <;> ext a <;> rfl
  right_inv f := by
    apply Finsupp.ext
    intro a
    rfl

def tupleEquiv : Tuple S ≃ (OutsidePrime S →₀ PrimeIndex) :=
  (Equiv.prodCongr (sqfEquiv S)
    (Equiv.prodCongr (extEquiv S) (Equiv.prodCongr (extEquiv S) (extEquiv S)))).trans
    ((Equiv.prodCongr (Equiv.refl _) ((Equiv.prodCongr (Equiv.refl _) zipEquiv).trans
      zipEquiv)).trans zipEquiv)

theorem tupleEquiv_counts (p : Tuple S) (v : OutsidePrime S) :
    ((tupleEquiv S p v).1 : ℕ) = (UniqueFactorizationMonoid.normalizedFactors p.1.1).count v.1.asIdeal ∧
    (tupleEquiv S p v).2.1 = (UniqueFactorizationMonoid.normalizedFactors p.2.1.1).count v.1.asIdeal ∧
    (tupleEquiv S p v).2.2.1 = (UniqueFactorizationMonoid.normalizedFactors p.2.2.1.1).count v.1.asIdeal ∧
    (tupleEquiv S p v).2.2.2 = (UniqueFactorizationMonoid.normalizedFactors p.2.2.2.1).count v.1.asIdeal := by
  exact ⟨sqfFactors_val S p.1 v, rfl, rfl, rfl⟩

end ArtinPrimitiveRoots.Proofs.a2_euler_sol.e_b
