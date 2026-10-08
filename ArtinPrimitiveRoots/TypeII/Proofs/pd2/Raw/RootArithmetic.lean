import ArtinPrimitiveRoots.TypeII.PD.Defs

namespace ArtinPrimitiveRoots.TypeII.PD

lemma pd2a_boundedNatPair_finite (U V : ℝ) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (P : ℕ × ℕ → Prop)
    (h₁ : ∀ z, P z → (z.1 : ℝ) ≤ U) (h₂ : ∀ z, P z → (z.2 : ℝ) ≤ V) :
    {z : ℕ × ℕ | P z}.Finite := by
  let box := (Finset.range (⌊U⌋₊ + 1)) ×ˢ (Finset.range (⌊V⌋₊ + 1))
  have hsub : {z : ℕ × ℕ | P z} ⊆ (box : Set (ℕ × ℕ)) := by
    intro z hz
    change z ∈ box
    rw [Finset.mem_product]
    constructor
    · simpa using Nat.lt_succ_of_le ((Nat.le_floor_iff hU).2 (h₁ z hz))
    · simpa using Nat.lt_succ_of_le ((Nat.le_floor_iff hV).2 (h₂ z hz))
  exact box.finite_toSet.subset hsub

lemma pd2a_rootResidueSet_finite (U V : ℝ) (hU : 0 < U) (hV : 0 < V)
    (S : ℕ) (g₀ : Matrix (Fin 2) (Fin 2) (ZMod S))
    (l₁ r₁ l₂ r₂ l₃ r₃ : ℝ) (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    {uv : ℕ × ℕ | Nat.Coprime uv.1 uv.2 ∧
      l₁ ≤ (uv.1 : ℝ) / U ∧ (uv.1 : ℝ) / U ≤ r₁ ∧
      l₂ ≤ (uv.2 : ℝ) / V ∧ (uv.2 : ℝ) / V ≤ r₂ ∧
      ∃ c d : ℤ, (uv.1 : ℤ) * d - (uv.2 : ℤ) * c = 1 ∧
        0 ≤ c ∧ c < uv.1 ∧ l₃ ≤ (c : ℝ) / uv.1 ∧ (c : ℝ) / uv.1 ≤ r₃ ∧
          g₀ 0 0 = (uv.1 : ZMod S) ∧ g₀ 0 1 = (c : ZMod S) ∧
            g₀ 1 0 = (uv.2 : ZMod S) ∧ g₀ 1 1 = (d : ZMod S)}.Finite := by
  apply pd2a_boundedNatPair_finite (r₁ * U) (r₂ * V)
    (mul_nonneg hr₁ hU.le) (mul_nonneg hr₂ hV.le)
  · intro uv huv
    rcases huv with ⟨_, _, huv, _, _, _⟩
    exact (div_le_iff₀ hU).mp huv
  · intro uv huv
    rcases huv with ⟨_, _, _, _, hv, _⟩
    exact (div_le_iff₀ hV).mp hv

lemma pd2a_root_completion_exists (u v : ℕ) (hu : 0 < u)
    (hcop : Nat.Coprime u v) :
    ∃ c d : ℤ, (u : ℤ) * d - (v : ℤ) * c = 1 ∧ 0 ≤ c ∧ c < (u : ℤ) := by
  have hcopInt : Int.gcd (u : ℤ) (v : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hcop.gcd_eq_one
  have hbez : (u : ℤ) * Int.gcdA (u : ℤ) (v : ℤ) +
      (v : ℤ) * Int.gcdB (u : ℤ) (v : ℤ) = 1 := by
    have h := Int.gcd_eq_gcd_ab (u : ℤ) (v : ℤ)
    rw [hcopInt] at h
    exact h.symm
  let c : ℤ := (-Int.gcdB (u : ℤ) (v : ℤ)) % (u : ℤ)
  let d : ℤ := Int.gcdA (u : ℤ) (v : ℤ) - (v : ℤ) *
    ((-Int.gcdB (u : ℤ) (v : ℤ)) / (u : ℤ))
  have huInt : 0 < (u : ℤ) := by exact_mod_cast hu
  have hcmod : c + (u : ℤ) *
      ((-Int.gcdB (u : ℤ) (v : ℤ)) / (u : ℤ)) =
      -Int.gcdB (u : ℤ) (v : ℤ) := by
    dsimp [c]
    exact Int.emod_add_mul_ediv _ _
  have hc0 : 0 ≤ c := by
    dsimp [c]
    exact Int.emod_nonneg _ (by exact_mod_cast hu.ne')
  have hc1 : c < (u : ℤ) := by
    dsimp [c]
    exact Int.emod_lt_of_pos _ huInt
  have hdet : (u : ℤ) * d - (v : ℤ) * c = 1 := by
    dsimp [d]
    nlinarith [hbez, hcmod]
  exact ⟨c, d, hdet, hc0, hc1⟩

lemma pd2a_root_completion_unique (u v : ℕ) (hu : 0 < u)
    (hcop : Nat.Coprime u v) (c₁ d₁ c₂ d₂ : ℤ)
    (h₁ : (u : ℤ) * d₁ - (v : ℤ) * c₁ = 1)
    (h₂ : (u : ℤ) * d₂ - (v : ℤ) * c₂ = 1)
    (hc₁lo : 0 ≤ c₁) (hc₁hi : c₁ < (u : ℤ))
    (hc₂lo : 0 ≤ c₂) (hc₂hi : c₂ < (u : ℤ)) :
    c₁ = c₂ ∧ d₁ = d₂ := by
  have hcopInt : Int.gcd (u : ℤ) (v : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact hcop.gcd_eq_one
  have hdiv : (u : ℤ) ∣ (v : ℤ) * (c₁ - c₂) := by
    refine ⟨d₁ - d₂, ?_⟩
    nlinarith [h₁, h₂]
  have hcdiv : (u : ℤ) ∣ c₁ - c₂ :=
    Int.dvd_of_dvd_mul_left_of_gcd_one (by simpa [mul_comm] using hdiv) hcopInt
  have habs : |c₁ - c₂| < (u : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hC : c₁ = c₂ := by
    have hz := Int.eq_zero_of_abs_lt_dvd hcdiv habs
    exact sub_eq_zero.mp hz
  have hDmul : (u : ℤ) * d₁ = (u : ℤ) * d₂ := by
    nlinarith [h₁, h₂, hC]
  have hD : d₁ = d₂ :=
    mul_left_cancel₀ (by exact_mod_cast (Nat.ne_of_gt hu)) hDmul
  exact ⟨hC, hD⟩


lemma pd2a_root_completion_exists_unique (u v : ℕ) (hu : 0 < u)
    (hcop : Nat.Coprime u v) :
    ∃! cd : ℤ × ℤ, (u : ℤ) * cd.2 - (v : ℤ) * cd.1 = 1 ∧
      0 ≤ cd.1 ∧ cd.1 < (u : ℤ) := by
  obtain ⟨c, d, hdet, hc0, hc1⟩ := pd2a_root_completion_exists u v hu hcop
  refine ⟨(c, d), ⟨hdet, hc0, hc1⟩, ?_⟩
  rintro ⟨c', d'⟩ ⟨hdet', hc0', hc1'⟩
  obtain ⟨rfl, rfl⟩ := pd2a_root_completion_unique u v hu hcop
    c' d' c d hdet' hdet hc0' hc1' hc0 hc1
  rfl

lemma pd2a_root_det_congruence (u v S : ℕ) (hu : 0 < u) (c d d₀ : ℤ)
    (hdet : (u : ℤ) * d - (v : ℤ) * c = 1) :
    ((d : ZMod S) = (d₀ : ZMod S)) ↔
      ((c * (v : ℤ) : ℤ) : ZMod (u * S)) =
        (((u : ℤ) * d₀ - 1 : ℤ) : ZMod (u * S)) := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub, ZMod.intCast_eq_intCast_iff_dvd_sub]
  have heq : (u : ℤ) * d₀ - 1 - c * (v : ℤ) = (u : ℤ) * (d₀ - d) := by
    nlinarith [hdet]
  rw [heq, Nat.cast_mul, mul_dvd_mul_iff_left (by exact_mod_cast hu.ne')]

end ArtinPrimitiveRoots.TypeII.PD
