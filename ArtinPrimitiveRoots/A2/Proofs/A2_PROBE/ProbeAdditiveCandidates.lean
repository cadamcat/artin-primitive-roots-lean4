import ArtinPrimitiveRoots.A2.Poisson.Results
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.ProbeFrequencySeparation
import ArtinPrimitiveRoots.A2.Proofs.A2_PROBE.ProbeResidueLift

set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.a2_probe_sol

open ArtinPrimitiveRoots A1 A2

variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}

/-- Select a finite set of distinct additive frequency classes from the exact
reduced denominator/residue labels. -/
theorem probe_additive_candidates {D : FieldData F} {S : SData F CE condη}
    {H : HilbertData F} {Bd : BData S H} {bc : BalancedChoices D S H Bd}
    (E : ExteriorArithmetic D S H Bd bc) (P : Finset S.ExtIdeal) (V : ℝ)
    (hcutoff : ∀ s ∈ P, idealNorm s.1 ≤ V) :
    let L := Σ s : {s : S.ExtIdeal // s ∈ P},
      {d : ResidueRing E s.1 // IsUnit d}
    ∃ α : L → S.FS, Function.Injective α ∧
      (∀ p, α p ∈ AdditiveCandidates D S bc V) ∧
      (∀ p, SameModuloSIntegers S (α p)
        (S.diag ((p.2.1.out : F) / (bc.gen p.1.1 : F)))) ∧
      ∃ Q : Finset S.FS,
        (∀ x, x ∈ Q ↔ ∃ p, α p = x) ∧
        ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → ¬ SameModuloSIntegers S x y := by
  let L := Σ s : {s : S.ExtIdeal // s ∈ P},
    {d : ResidueRing E s.1 // IsUnit d}
  let lift (p : L) := probe_residue_lift E p.1.1 p.2.1 p.2.2
  let c (p : L) : 𝓞 F := (lift p).choose
  have hc (p : L) : IsCoprime (Ideal.span {c p}) p.1.1.1 ∧
      ∃ r : S.R, (p.2.1.out : F) - algebraMap (𝓞 F) F (c p) =
        (bc.gen p.1.1 : F) * (r : F) := (lift p).choose_spec
  let r (p : L) : S.R := (hc p).2.choose
  have hr (p : L) : (p.2.1.out : F) - algebraMap (𝓞 F) F (c p) =
      (bc.gen p.1.1 : F) * (r p : F) := (hc p).2.choose_spec
  let f (p : L) : F := algebraMap (𝓞 F) F (c p) / (bc.gen p.1.1 : F)
  let α (p : L) : S.FS := S.diag (f p)
  have hdelta (p : L) : (p.2.1.out : F) / (bc.gen p.1.1 : F) - f p = (r p : F) := by
    change (p.2.1.out : F) / (bc.gen p.1.1 : F) -
      algebraMap (𝓞 F) F (c p) / (bc.gen p.1.1 : F) = (r p : F)
    rw [← sub_div, hr p]
    field_simp [Units.ne_zero (bc.gen p.1.1)]
  have hsep (p q : L) (hmod : SameModuloSIntegers S (α p) (α q)) : p = q := by
    obtain ⟨x, hx⟩ := hmod
    have hf : f p - f q = (x : F) := S.diag.injective (by
      simpa only [α, map_sub] using hx)
    have horig : (p.2.1.out : F) / (bc.gen p.1.1 : F) -
        (q.2.1.out : F) / (bc.gen q.1.1 : F) ∈ S.R := by
      have hF : (p.2.1.out : F) / (bc.gen p.1.1 : F) -
          (q.2.1.out : F) / (bc.gen q.1.1 : F) =
            (x : F) + (r p : F) - (r q : F) := by
        linear_combination hdelta p - hdelta q + hf
      rw [hF]
      exact S.R.sub_mem (S.R.add_mem x.property (r p).property) (r q).property
    obtain ⟨hs, hd⟩ := probe_residue_frequencies_separated E
      p.1.1 q.1.1 p.2.1 q.2.1 p.2.2 q.2.2 horig
    rcases p with ⟨⟨s, hsP⟩, ⟨d, hdU⟩⟩
    rcases q with ⟨⟨t, htP⟩, ⟨e, heU⟩⟩
    dsimp only at hs hd
    cases hs
    have hde : d = e := eq_of_heq hd
    subst e
    rfl
  have hinj : Function.Injective α := by
    intro p q hpq
    apply hsep p q
    refine ⟨0, ?_⟩
    simp [hpq]
  have hcandidate (p : L) : α p ∈ AdditiveCandidates D S bc V :=
    Or.inr ⟨p.1.1, hcutoff p.1.1 p.1.2, c p, (hc p).1, rfl⟩
  have hmod (p : L) : SameModuloSIntegers S (α p)
      (S.diag ((p.2.1.out : F) / (bc.gen p.1.1 : F))) := by
    refine ⟨-r p, ?_⟩
    change S.diag (f p) - S.diag ((p.2.1.out : F) / (bc.gen p.1.1 : F)) =
      S.diag (-(r p : F))
    rw [← map_sub]
    apply congrArg S.diag
    linear_combination -hdelta p
  let (s : S.ExtIdeal) : Fintype (ResidueRing E s) := E.residueFinite s
  let : Fintype L := inferInstance
  let Q : Finset S.FS := Finset.univ.image α
  refine ⟨α, hinj, hcandidate, hmod, Q, ?_, ?_⟩
  · intro x
    simp only [Q, Finset.mem_image, Finset.mem_univ, true_and]
    rfl
  · intro x hx y hy hne hmodxy
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hy
    exact hne (congrArg α (hsep p q hmodxy))

end ArtinPrimitiveRoots.Proofs.a2_probe_sol
