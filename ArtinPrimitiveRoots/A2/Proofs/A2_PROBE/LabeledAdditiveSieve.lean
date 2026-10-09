import ArtinPrimitiveRoots.A2.Poisson.Results

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

open ArtinPrimitiveRoots A1 A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Transport the primal additive sieve to any finite family of distinct
frequency labels. The frozen additive sieve is the upstream analytic input. -/
theorem additive_sieve_labeled (D : FieldData F) (S : SData F CE condη)
    (H : HilbertData F) (A : AddCharData F) (Bd : BData S H)
    (bc : BalancedChoices D S H Bd) (K : Set S.FS) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ N V : ℝ, (hN : 2 ≤ N) → (hV : 2 ≤ V) →
      ∀ (L : Type) [Fintype L] (α : L → S.FS),
        (∀ p, α p ∈ AdditiveCandidates D S bc V) →
        (∀ p q, p ≠ q → ¬ SameModuloSIntegers S (α p) (α q)) →
        ∀ c : L → ℂ,
          (∑' m : {m : S.R // InAdditiveWindow D S K N (by linarith [hN]) m},
            ‖∑ p : L, c p * additivePhase S A m.1 (α p)‖ ^ 2) ≤
            C * (N + V ^ 2) * ∑ p : L, ‖c p‖ ^ 2 := by
  obtain ⟨C, hC, hSieve⟩ := lem_additive_sieve D S H A Bd bc K hK
  refine ⟨C, hC, ?_⟩
  intro N V hN hV L _ α hα hsep c
  have hinj : Function.Injective α := by
    intro p q hpq
    by_contra hne
    apply hsep p q hne
    refine ⟨0, ?_⟩
    simp [hpq]
  let Q : Finset S.FS := Finset.univ.image α
  have hQ : (∀ x ∈ Q, x ∈ AdditiveCandidates D S bc V) ∧
      (∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → ¬ SameModuloSIntegers S x y) := by
    constructor
    · intro x hx
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
      exact hα p
    · intro x hx y hy hne
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hy
      exact hsep p q (fun hpq => hne (congrArg α hpq))
  let b (x : S.FS) : ℂ := if h : ∃ p, α p = x then c h.choose else 0
  have hb (p : L) : b (α p) = c p := by
    have hp : ∃ q, α q = α p := ⟨p, rfl⟩
    simp only [b, dite_eq_left hp]
    exact congrArg c (hinj hp.choose_spec)
  have hsum (g : S.FS → ℂ) : (∑ x ∈ Q, b x * g x) = ∑ p : L, c p * g (α p) := by
    dsimp only [Q]
    rw [Finset.sum_image (fun p _ q _ h => hinj h)]
    exact Finset.sum_congr rfl fun p _ => by rw [hb p]
  have hmass : (∑ x ∈ Q, ‖b x‖ ^ 2) = ∑ p : L, ‖c p‖ ^ 2 := by
    dsimp only [Q]
    rw [Finset.sum_image (fun p _ q _ h => hinj h)]
    exact Finset.sum_congr rfl fun p _ => by rw [hb p]
  have hbound := (hSieve N V hN hV Q hQ b).1
  simpa only [hsum, hmass] using hbound

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
