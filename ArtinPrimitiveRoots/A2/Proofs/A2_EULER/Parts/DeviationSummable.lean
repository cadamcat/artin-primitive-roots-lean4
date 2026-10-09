import ArtinPrimitiveRoots.A2.Proofs.A2_EULER.Definitions

set_option autoImplicit false
set_option maxHeartbeats 800000
open NumberField IsDedekindDomain MeasureTheory
open scoped Classical Topology
noncomputable section
namespace ArtinPrimitiveRoots.Proofs.a2_euler_sol
open ArtinPrimitiveRoots A1 A2
variable {F : Type} [Field F] [NumberField F]
variable {CE : ℕ} {condη : Ideal (𝓞 F)}
variable {D : FieldData F} {S : SData F CE condη} {H : HilbertData F}
  {Bd : BData S H} {A : AddCharData F} {ϑ : HeckeChar F}
  {bc : BalancedChoices D S H Bd} {μ : ∀ v : FinPlace F, Theta.LocHaar v}
  {v0 : InfinitePlace F}
variable (R : ReflectionSetup D S H Bd A ϑ bc μ v0)
  (η : HeckeChar F) (U : FrequencyData S D η)

theorem deviation_summable (C Q0 : ℝ) (hb : HasPoHLocalBounds R η U C Q0)
    (u : U.U) (p : Triple) (hp : eulerNeighborhood p) :
    Summable (fun v : {v : FinPlace F // v ∉ S.Sf} =>
      ‖normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2) - 1‖) := by
  classical
  let α := {v : FinPlace F // v ∉ S.Sf}
  let dev : α → ℝ := fun v =>
    ‖normalizedLocal R η U u v.1 v.2 (p 0) (p 1) (p 2) - 1‖
  have hQ0 : 0 ≤ Q0 := le_trans (by norm_num) hb.2.1.le
  have hlowAll : {v : FinPlace F | qI v.asIdeal ≤ Q0}.Finite := by
    apply Set.Finite.of_injOn (f := fun v : FinPlace F => v.asIdeal)
      (s := {v : FinPlace F | qI v.asIdeal ≤ Q0})
      (t := {I : Ideal (𝓞 F) | Ideal.absNorm I ≤ ⌊Q0⌋₊}) ?_ ?_
      (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 F) ⌊Q0⌋₊)
    · intro v hv
      change Ideal.absNorm v.asIdeal ≤ ⌊Q0⌋₊
      exact (Nat.le_floor_iff hQ0).mpr (by simpa [qI] using hv)
    · intro v hv w hw h
      exact HeightOneSpectrum.ext h
  have hlow : {v : α | qI v.1.asIdeal ≤ Q0}.Finite :=
    hlowAll.preimage (f := fun v : α => v.1) (by
      intro v hv w hw h
      exact Subtype.ext h)
  let J : FractionalIdeal (nonZeroDivisors (𝓞 F)) F :=
    FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) (U.repr u : F)
  let c : FinPlace F → ℤ := fun v => FractionalIdeal.count F v J
  have hc : (Function.support c).Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors J)
  have hbadAll : {v : FinPlace F | frequencyValuation η U u v ≠ 0}.Finite := by
    apply hc.subset
    intro v hv
    change c v ≠ 0
    intro hzero
    apply hv
    simp [frequencyValuation, c, J, hzero]
  have hbad : {v : α | frequencyValuation η U u v.1 ≠ 0}.Finite :=
    hbadAll.preimage (f := fun v : α => v.1) (by
      intro v hv w hw h
      exact Subtype.ext h)
  let exceptional : Set α :=
    {v | frequencyValuation η U u v.1 ≠ 0} ∪ {v | qI v.1.asIdeal ≤ Q0}
  have hexceptional : exceptional.Finite := by
    exact hbad.union hlow
  let s : ℝ := 1 + 1 / 4000
  have hs₁ : 1 < s := by norm_num [s]
  have hcount := a2_bridge_COUNT_summable S s hs₁
  have hcountExt : Summable (fun I : S.ExtIdeal => qI I.1 ^ (-s)) := by
    simpa [qI, idealNorm] using hcount
  let ext : α → S.ExtIdeal := fun v => R.exterior.prime v.1 v.2
  have hext : Function.Injective ext := by
    intro v w h
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    have hval := congrArg Subtype.val h
    simpa [ext, R.exterior.prime_val] using hval
  have hcountPlaces : Summable (fun v : α => qI (ext v).1 ^ (-s)) :=
    hcountExt.comp_injective hext
  have hmajor : Summable (fun v : α => qI v.1.asIdeal ^ (-s)) := by
    simpa [ext, R.exterior.prime_val] using hcountPlaces
  have hmajorC : Summable (fun v : α => C * qI v.1.asIdeal ^ (-s)) :=
    hmajor.mul_left C
  apply Summable.add_compl (s := hexceptional.toFinset) Summable.of_finite
  apply Summable.of_nonneg_of_le (fun v => norm_nonneg _) ?_ (hmajorC.subtype _)
  intro v
  have hvNot : v.1 ∉ exceptional := by
    intro hvE
    exact v.2 (hexceptional.mem_toFinset.mpr hvE)
  have hfreq : frequencyValuation η U u v.1.1 = 0 := by
    by_contra hne
    exact hvNot (Or.inl hne)
  have hQ : Q0 < qI v.1.1.asIdeal := by
    exact lt_of_not_ge (fun hle => hvNot (Or.inr hle))
  have hlocal := hb.2.2 u v.1.1 v.1.2 p hQ hp
  have hbound := hlocal.2
  convert hbound using 1 <;> norm_num [dev, s, hfreq]

end ArtinPrimitiveRoots.Proofs.a2_euler_sol
