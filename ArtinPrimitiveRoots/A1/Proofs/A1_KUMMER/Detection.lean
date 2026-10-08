import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.Types
import ArtinPrimitiveRoots.A1.Proofs.A1_KUMMER.ContinuousCharacters

/-! Global sixth-power detection from the Hilbert character kernel. -/

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped Classical

noncomputable section

namespace ArtinPrimitiveRoots.A1.KummerProofs

variable {F : Type} [Field F] [NumberField F]

theorem hilbert_global_sixth_detection (D : FieldData F) (H : HilbertData F)
    (a : Fˣ) (ha : ∀ (P : FinPlace F) (x : (P.adicCompletion F)ˣ),
      H.hilb P (toLoc P a) x = 1) : ∃ t : Fˣ, a = t ^ 6 := by
  classical
  let I := FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (a : F)
  let T := (Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)).toFinset
  let CE := T.sup (fun P : FinPlace F => Ideal.absNorm P.asIdeal)
  obtain ⟨S⟩ := SData.nonempty (F := F) CE ⊤ top_ne_bot
  have hTS : T ⊆ S.Sf := by
    intro P hP
    exact S.euler_mem P
      (Finset.le_sup (f := fun Q : FinPlace F => Ideal.absNorm Q.asIdeal) hP)
  have hcount (P : FinPlace F) (hP : P ∉ S.Sf) :
      FractionalIdeal.count F P I = 0 := by
    have hPT : P ∉ T := fun h => hP (hTS h)
    simpa only [T, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hPT
  have htop : S.IsExterior (⊤ : Ideal (𝓞 F)) := by
    refine ⟨top_ne_bot, ?_⟩
    intro P _ hP
    exact P.isPrime.ne_top (top_le_iff.mp hP)
  have hgena : S.IsGen (a : F) ⊤ := by
    refine ⟨htop, a.ne_zero, ?_⟩
    intro P hP
    rw [FractionalIdeal.coeIdeal_top, FractionalIdeal.count_one]
    exact hcount P hP
  have hgenone : S.IsGen (1 : F) ⊤ := by
    refine ⟨htop, one_ne_zero, ?_⟩
    intro P _
    rw [FractionalIdeal.spanSingleton_one, FractionalIdeal.coeIdeal_top]
  obtain ⟨B⟩ := BData.nonempty D S H
  choose c hc using fun P : S.Sf => H.nondeg P.1 (toLoc P.1 a) (ha P.1)
  choose z hz using fun w : InfinitePlace F =>
    IsAlgClosed.exists_pow_nat_eq (w.embedding (a : F)) (n := 6) (by decide)
  let r : S.FS := (fun P => (c P : P.1.adicCompletion F), fun w => z w)
  have hr : r ^ 6 = S.diag (a : F) := by
    apply Prod.ext
    · funext P
      exact (congrArg (fun x : (P.1.adicCompletion F)ˣ => (x : P.1.adicCompletion F))
        (hc P)).symm
    · funext w
      exact hz w
  have hrunit : IsUnit r := by
    apply (isUnit_pow_iff (by decide : (6 : ℕ) ≠ 0)).mp
    rw [hr]
    exact (S.diagU a).isUnit
  have hdiag : S.diagU a = hrunit.unit ^ 6 := by
    apply Units.ext
    change S.diag (a : F) = (hrunit.unit : S.FS) ^ 6
    rw [hrunit.unit_spec]
    exact hr.symm
  have hclass : (QuotientGroup.mk (S.diagU a) : S.V) = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    exact ⟨hrunit.unit, hdiag.symm⟩
  have hallowa : B.Allowed a := by
    change (QuotientGroup.mk (S.diagU a) : S.V) ∈ B.B
    rw [hclass]
    exact B.B.one_mem
  have hallowone : B.Allowed (1 : Fˣ) := by
    simp [BData.Allowed]
  obtain ⟨t, _, ht⟩ := B.allowed_unique ⊤ a 1 ⟨hgena, hallowa⟩ ⟨hgenone, hallowone⟩
  exact ⟨t, by simpa only [mul_one] using ht⟩

theorem kummer_realization_eq_iff (D : FieldData F) (H : HilbertData F)
    (a b : Fˣ) (κa κb : KummerChar F)
    (haInf : ∀ (w : InfinitePlace F) (x : w.Completionˣ), infiniteComponent κa w x = 1)
    (hbInf : ∀ (w : InfinitePlace F) (x : w.Completionˣ), infiniteComponent κb w x = 1)
    (haloc : ∀ P : FinPlace F, localComponent κa P = kummerLocal D H P (toLoc P a))
    (hbloc : ∀ P : FinPlace F, localComponent κb P = kummerLocal D H P (toLoc P b)) :
    κa = κb ↔ ∃ t : Fˣ, a / b = t ^ 6 := by
  classical
  let pairLeft (P : FinPlace F) (x : (P.adicCompletion F)ˣ) :
      (P.adicCompletion F)ˣ →* rootsOfUnity 6 F :=
    MonoidHom.mk' (fun c => H.hilb P c x) (fun c d => H.mul_left P c d x)
  have hdiv (P : FinPlace F) (x : (P.adicCompletion F)ˣ) :
      H.hilb P (toLoc P (a / b)) x =
        H.hilb P (toLoc P a) x / H.hilb P (toLoc P b) x := by
    change pairLeft P x (toLoc P (a / b)) =
      pairLeft P x (toLoc P a) / pairLeft P x (toLoc P b)
    rw [map_div, map_div]
  constructor
  · intro heq
    apply hilbert_global_sixth_detection D H (a / b)
    intro P x
    have hvalues : kummerLocal D H P (toLoc P a) x =
        kummerLocal D H P (toLoc P b) x := by
      rw [← haloc P, ← hbloc P, heq]
    have hhilb : H.hilb P (toLoc P a) x = H.hilb P (toLoc P b) x := by
      apply Subtype.ext
      apply Units.ext
      apply D.σ0.injective
      exact congrArg (fun z : ℂˣ => (z : ℂ)) hvalues
    rw [hdiv, hhilb, div_self']
  · rintro ⟨t, ht⟩
    have hlocals (P : FinPlace F) : localComponent κa P = localComponent κb P := by
      rw [haloc P, hbloc P]
      apply MonoidHom.ext
      intro x
      have hpower : H.hilb P (toLoc P (a / b)) x = 1 :=
        H.sixth_power P _ x ⟨toLoc P t, by rw [ht, map_pow]⟩
      rw [hdiv] at hpower
      have hhilb := div_eq_one.mp hpower
      change Units.map D.σ0.toMonoidHom (H.hilb P (toLoc P a) x : Fˣ) =
        Units.map D.σ0.toMonoidHom (H.hilb P (toLoc P b) x : Fˣ)
      rw [hhilb]
    apply kummer_char_ext κa κb
    · intro w x
      rw [haInf, hbInf]
    · intro P x
      exact congrArg (fun f : (P.adicCompletion F)ˣ →* ℂˣ => f x) (hlocals P)

end ArtinPrimitiveRoots.A1.KummerProofs
