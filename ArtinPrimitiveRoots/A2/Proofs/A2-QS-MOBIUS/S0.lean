import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MOBIUS».Defs
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».M0
import ArtinPrimitiveRoots.A2.Proofs.«A2-QS-MATRIX».M1

/-!
# A2-QS-MOBIUS, part S0: multiplicativity, class/dyad slicing, gcd expansion and descent

Guide: `runs/lanes/sol-thin-found/PROOFS.md:396-408` (S0) and G1 (found:613-615) specialised to
trivial ray factor.  The family identities are derived prime by prime from `reciprocity`
(trivial factor), `idealValue` multiplicativity (`qs_idealValue_mul_M0`) and ramification at the
primitive conductor (`qs_idealValue_eq_zero_of_conductor_M0`); rows are coprime to `m` and `qS`.
-/

set_option autoImplicit false

open scoped NumberField ComplexConjugate
open NumberField IsDedekindDomain
open ClassFieldTheory

noncomputable section

namespace ArtinPrimitiveRoots.A2

variable {K : Type} [Field K] [NumberField K]
variable {m : ClassFieldTheory.RayClassModulus K} {qS : Ideal (𝓞 K)}

/-- S0 (IMPL): family multiplicativity on rows coprime to `m` and `qS` (trivial ray factor):
`χ_{cd}(a) = χ_c(a) χ_d(a)` for coprime admissible `c, d`.  Prime by prime:
`χ_{cd}(P) = χ_P(cd) = χ_P(c) χ_P(d) = χ_c(P) χ_d(P)` for `P ∤ cd`, and both sides vanish at
`P ∣ cd`. -/
theorem qs_family_mul_S0 (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (c d : Ideal (𝓞 K)) (hc : QSAdm m qS c) (hd : QSAdm m qS d) (hcd : IsCoprime c d)
    (a : Ideal (𝓞 K)) (ha : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a) (haq : IsCoprime a qS) :
    (F.character (c * d)).idealValue a =
      (F.character c).idealValue a * (F.character d).idealValue a := by
  sorry

open Classical in
/-- S0 (IMPL): the gcd identity.  For pairwise coprime admissible `g, c, d` and a row `a`
coprime to `m` and `qS`:
`χ_{gc}(a) conj(χ_{gd}(a)) = 1_{(a,g)=1} · ψ_{c,d}(a)`, `ψ_{c,d} = χ_c χ_d⁻¹`
(ramified × unramified is ramified at `P ∣ cd`; `χ_g(a)² = 1_{(a,g)=1}`). -/
theorem qs_gcd_pair_identity_S0 (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (g c d : Ideal (𝓞 K)) (hg : QSAdm m qS g) (hc : QSAdm m qS c) (hd : QSAdm m qS d)
    (hgc : IsCoprime g c) (hgd : IsCoprime g d) (hcd : IsCoprime c d)
    (a : Ideal (𝓞 K)) (ha : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m a) (haq : IsCoprime a qS) :
    (F.character (g * c)).idealValue a * conj ((F.character (g * d)).idealValue a) =
      if IsCoprime a g then (qsPairChar F c d).idealValue a else 0 := by
  sorry

/-- S0 (IMPL): `B₂` is controlled by energies: `qsHighEnergy ≤ qsHighNorm · ‖z‖²` for columns
of norm `≤ N`, and `qsHighNorm` is the least such bound. -/
theorem qs_high_norm_energy_S0 (F : QSFamily m qS) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M N κ : ℝ) (hM : 0 < M) :
    (∀ z : Ideal (𝓞 K) → ℂ,
      qsHighEnergy F W M κ (qsUpTo m qS N) z ≤
        qsHighNorm F W M N κ * ∑ c ∈ qsUpTo m qS N, ‖z c‖ ^ 2) ∧
    (∀ B : ℝ, 0 ≤ B → (∀ z : Ideal (𝓞 K) → ℂ,
      qsHighEnergy F W M κ (qsUpTo m qS N) z ≤ B * ∑ c ∈ qsUpTo m qS N, ‖z c‖ ^ 2) →
        qsHighNorm F W M N κ ≤ B) := by
  sorry

/-- S0 (IMPL): class and dyad slicing (Cauchy–Schwarz over the finite ray class group and over
the `⌈log₂ N⌉₊ + 1` column dyads `N/2^{j+1} < N c ≤ N/2^j`): the up-to columns split into at
most `h_m (⌈log₂ N⌉₊ + 1)` pairwise disjoint parts, each inside one ray class and one dyad
`(n, 2n]`, `n = N/2^{j+1}`, and the high-core energy is at most the number of parts times the
sum of the part energies. -/
theorem qs_class_dyad_slice_S0 (F : QSFamily m qS) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M N κ : ℝ) (hN : 1 ≤ N) (z : Ideal (𝓞 K) → ℂ) :
    ∃ parts : Finset (Finset (Ideal (𝓞 K))),
      ((parts.card : ℕ) : ℝ) ≤
          (Nat.card (ClassFieldTheory.RayClassGroup m) : ℝ) *
            ((Nat.ceil (Real.logb 2 N) + 1 : ℕ) : ℝ) ∧
      (∀ P ∈ parts, P ⊆ qsUpTo m qS N) ∧
      (∀ P ∈ parts, ∀ Q ∈ parts, P ≠ Q → Disjoint P Q) ∧
      (∀ P ∈ parts, ∃ j : ℕ, ∀ c ∈ P, N / 2 ^ (j + 1) < qsN c ∧ qsN c ≤ N / 2 ^ j) ∧
      (∀ P ∈ parts, ∀ c ∈ P, ∀ d ∈ P, ∃ (hc : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m c)
        (hd : ArtinPrimitiveRoots.Hecke.IsCoprimeTo m d),
        ArtinPrimitiveRoots.Hecke.rayClass m c hc = ArtinPrimitiveRoots.Hecke.rayClass m d hd) ∧
      qsHighEnergy F W M κ (qsUpTo m qS N) z ≤
        ((parts.card : ℕ) : ℝ) * ∑ P ∈ parts, qsHighEnergy F W M κ P z := by
  sorry

open Classical in
/-- S0 (IMPL): exact gcd expansion of the energy of an admissible column set
(`|Σ_c z_c χ_c(a)|² = Σ_{c,d} z_c conj(z_d) χ_c(a) conj(χ_d(a))`, grouped by `g = c ⊔ d`). -/
theorem qs_gcd_expansion_S0 (F : QSFamily m qS) (W : ℝ → ℝ) (hW : IsCapWeight W)
    (M κ : ℝ) (hM : 0 < M) (cols : Finset (Ideal (𝓞 K)))
    (hcols : ∀ c ∈ cols, QSAdm m qS c) (z : Ideal (𝓞 K) → ℂ) :
    ((qsHighEnergy F W M κ cols z : ℝ) : ℂ) =
      ∑ g ∈ (cols ×ˢ cols).image (fun p => p.1 ⊔ p.2), qsGcdBlock F W M κ g cols z := by
  sorry

open Classical in
/-- S0 (IMPL): a gcd block is a residual block for the coprimality ideal `qsBadRad m qS * g`,
with residual columns `c' = c / g` (`c = g c'`) and shifted coefficients `z'(c') = z(g c')`. -/
theorem qs_residual_form_S0 (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (hqS : qS ≠ ⊥) (W : ℝ → ℝ) (hW : IsCapWeight W) (M κ : ℝ) (hM : 0 < M)
    (g : Ideal (𝓞 K)) (cols : Finset (Ideal (𝓞 K)))
    (hcols : ∀ c ∈ cols, QSAdm m qS c) (z : Ideal (𝓞 K) → ℂ) :
    ∃ (cols' : Finset (Ideal (𝓞 K))) (z' : Ideal (𝓞 K) → ℂ),
      (∀ c' ∈ cols', QSAdm m qS c' ∧ IsCoprime c' g ∧ g * c' ∈ cols ∧ z' c' = z (g * c')) ∧
      (∀ c ∈ cols, g ∣ c → ∃ c' ∈ cols', c = g * c') ∧
      qsGcdBlock F W M κ g cols z = qsResidualBlock F W M κ (qsBadRad m qS * g) cols' z' := by
  sorry

open Classical in
/-- S0 (IMPL): gcd descent (found:405-412).  Blocks with `N g > G` recombine, by Möbius
inversion on the divisor lattice and multiplicativity, into high-core energies of shifted
vectors at column length `≤ 2N/G`; the divisor multiplicities cost `N^η`. -/
theorem qs_gcd_descent_S0 (F : QSFamily m qS) (hrf : ∀ g h, F.rayFactor g h = 1)
    (W : ℝ → ℝ) (hW : IsCapWeight W) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M N G κ : ℝ) (cols : Finset (Ideal (𝓞 K))) (z : Ideal (𝓞 K) → ℂ),
      0 < M → 1 ≤ N → 1 ≤ G →
      (∀ c ∈ cols, QSAdm m qS c ∧ qsN c ≤ 2 * N) →
      ‖∑ g ∈ ((cols ×ˢ cols).image (fun p => p.1 ⊔ p.2)).filter (fun g => G < qsN g),
          qsGcdBlock F W M κ g cols z‖ ≤
        C * N ^ η * qsHighNorm F W M (2 * N / G) κ * ∑ c ∈ cols, ‖z c‖ ^ 2 := by
  sorry

end ArtinPrimitiveRoots.A2
