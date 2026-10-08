import ArtinPrimitiveRoots.Theta.Proofs.TH_COVER.Congruence

/-! Canonical congruence neighborhoods in GL₂ over a finite completion. -/

set_option autoImplicit false
open NumberField IsDedekindDomain Filter Topology
open scoped Classical
noncomputable section

namespace ArtinPrimitiveRoots.Proofs.th_cover_sol
open ArtinPrimitiveRoots.A1
variable {F : Type} [Field F] [NumberField F]

/-- Entrywise congruence sets are open and form a neighborhood basis at one in canonical GL₂. -/
theorem congruenceTopology (v : FinPlace F) :
    (∀ m : ℕ, IsOpen {g : GL (Fin 2) (v.adicCompletion F) | ∀ i j,
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j -
        (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ WithZero.exp (-(m : ℤ))}) ∧
    (∀ m0 : ℕ, ∀ U ∈ nhds (1 : GL (Fin 2) (v.adicCompletion F)),
      ∃ m : ℕ, m0 ≤ m ∧ {g : GL (Fin 2) (v.adicCompletion F) | ∀ i j,
        Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j -
          (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤
          WithZero.exp (-(m : ℤ))} ⊆ U) := by
  classical
  let K := v.adicCompletion F
  let Mat := Matrix (Fin 2) (Fin 2) K
  letI : Monoid Mat := inferInstanceAs (Monoid (Matrix (Fin 2) (Fin 2) (v.adicCompletion F)))
  let V : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  have hsurj : Function.Surjective V := v.valuedAdicCompletion_surjective F
  have scalarOpen (m : ℕ) : IsOpen {x : K | V x ≤ WithZero.exp (-(m : ℤ))} := by
    obtain ⟨π, hπ⟩ := hsurj (WithZero.exp (-(m : ℤ)))
    have hπv : V π ≠ 0 := by rw [hπ]; exact WithZero.exp_ne_zero
    have hπne : π ≠ 0 := V.ne_zero_iff.mp hπv
    have hγne : V.restrict π ≠ 0 := V.restrict.ne_zero_iff.mpr hπne
    have h := Valued.isOpen_closedBall K (Γ₀ := WithZero (Multiplicative ℤ))
      (r := V.restrict π) hγne
    convert h using 1
    ext x
    change V x ≤ WithZero.exp (-(m : ℤ)) ↔ V.restrict x ≤ V.restrict π
    rw [V.restrict_le_iff, hπ]
  have scalarNeighborhood (a : K) (U : Set K) (hU : U ∈ nhds a) :
      ∃ m : ℕ, ∀ x : K, V (x - a) ≤ WithZero.exp (-(m : ℤ)) → x ∈ U := by
    obtain ⟨γ, hγ⟩ := (Valued.mem_nhds (Γ₀ := WithZero (Multiplicative ℤ))).mp hU
    let γ' : (WithZero (Multiplicative ℤ))ˣ := Units.map
      (MonoidWithZeroHom.ValueGroup₀.embedding (f := .ofClass (Valued.v : Valuation K (WithZero (Multiplicative ℤ))))) γ
    let e : ℤ := WithZero.log (γ' : WithZero (Multiplicative ℤ))
    let m : ℕ := (1 - e).toNat + 1
    have hm : -(m : ℤ) < e := by dsimp [m]; omega
    refine ⟨m, ?_⟩
    intro x hx
    have hsmall : V (x - a) < (γ' : WithZero (Multiplicative ℤ)) := by
      apply hx.trans_lt
      rw [← WithZero.exp_log γ'.ne_zero]
      exact WithZero.exp_lt_exp.mpr hm
    have hsmall' : V.restrict (x - a) < γ := by
      rw [Valuation.restrict_lt_iff_lt_embedding]
      exact hsmall
    exact hγ hsmall'
  have matrixMono (m n : ℕ) (hmn : m ≤ n) (A : Mat)
      (hA : ∀ i j, V (A i j - (1 : Mat) i j) ≤ WithZero.exp (-(n : ℤ))) :
      ∀ i j, V (A i j - (1 : Mat) i j) ≤ WithZero.exp (-(m : ℤ)) := by
    intro i j
    exact (hA i j).trans (WithZero.exp_le_exp.mpr (by omega))
  have matrixNeighborhood (U : Set Mat) (hU : U ∈ nhds (1 : Mat)) :
      ∃ m : ℕ, ∀ A : Mat,
        (∀ i j, V (A i j - (1 : Mat) i j) ≤ WithZero.exp (-(m : ℤ))) → A ∈ U := by
    change U ∈ nhds ((1 : Mat) : Fin 2 → Fin 2 → K) at hU
    erw [nhds_pi (a := ((1 : Mat) : Fin 2 → Fin 2 → K))] at hU
    obtain ⟨I, s, hs, hSU⟩ := Filter.mem_pi'.mp hU
    have hrow (i : Fin 2) : ∃ J : Finset (Fin 2), ∃ r : Fin 2 → Set K,
        (∀ j, r j ∈ nhds ((1 : Mat) i j)) ∧ Set.pi (J : Set (Fin 2)) r ⊆ s i := by
      have hsi := hs i
      erw [nhds_pi (a := ((1 : Mat) i : Fin 2 → K))] at hsi
      exact Filter.mem_pi'.mp hsi
    choose J r hr hsub using hrow
    choose ms hms using fun i j => scalarNeighborhood ((1 : Mat) i j) (r i j) (hr i j)
    let m := max (ms 0 0) (max (ms 0 1) (max (ms 1 0) (ms 1 1)))
    have hmax : ∀ i j, ms i j ≤ m := by
      intro i j
      fin_cases i <;> fin_cases j <;> dsimp [m] <;> omega
    refine ⟨m, ?_⟩
    intro A hA
    apply hSU
    intro i hi
    apply hsub i
    intro j hj
    apply hms i j (A i j)
    exact (hA i j).trans (WithZero.exp_le_exp.mpr (by have hb := hmax i j; omega))
  have hopen : ∀ m : ℕ, IsOpen {g : GL (Fin 2) K | ∀ i j,
      V ((g : Mat) i j - (1 : Mat) i j) ≤ WithZero.exp (-(m : ℤ))} := by
    intro m
    have hval : Continuous (fun g : GL (Fin 2) K => (g : Mat)) := Units.continuous_val
    have hentry (i j : Fin 2) : IsOpen {g : GL (Fin 2) K |
        V ((g : Mat) i j - (1 : Mat) i j) ≤ WithZero.exp (-(m : ℤ))} :=
      (scalarOpen m).preimage ((hval.matrix_elem i j).sub continuous_const)
    have ho := isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hentry i j
    convert ho using 1
    ext g
    simp
  refine ⟨hopen, ?_⟩
  intro m0 U hU
  let tGL : TopologicalSpace (GL (Fin 2) (v.adicCompletion F)) := inferInstance
  let tv : TopologicalSpace (GL (Fin 2) (v.adicCompletion F)) :=
    TopologicalSpace.induced (fun g : GL (Fin 2) (v.adicCompletion F) => (g : Mat)) inferInstance
  let ti : TopologicalSpace (GL (Fin 2) (v.adicCompletion F)) :=
    TopologicalSpace.induced (fun g : GL (Fin 2) (v.adicCompletion F) => ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Mat)) inferInstance
  have hT : tGL = tv ⊓ ti := by
    simpa only [tGL, tv, ti] using (Units.topology_eq_inf (M := Mat))
  have hN : @nhds (GL (Fin 2) (v.adicCompletion F)) tGL 1 =
      Filter.comap (fun g : GL (Fin 2) (v.adicCompletion F) => (g : Mat)) (nhds (1 : Mat)) ⊓
        Filter.comap (fun g : GL (Fin 2) (v.adicCompletion F) => ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Mat)) (nhds (1 : Mat)) := by
    calc
      _ = @nhds (GL (Fin 2) (v.adicCompletion F)) (tv ⊓ ti) 1 :=
        congrArg (fun t : TopologicalSpace (GL (Fin 2) (v.adicCompletion F)) => @nhds _ t 1) hT
      _ = @nhds (GL (Fin 2) (v.adicCompletion F)) tv 1 ⊓
          @nhds (GL (Fin 2) (v.adicCompletion F)) ti 1 :=
        nhds_inf (t₁ := tv) (t₂ := ti) (a := (1 : GL (Fin 2) (v.adicCompletion F)))
      _ = _ := by simp only [tv, ti, nhds_induced, Units.val_one, inv_one]
  have hUinf := hN ▸ hU
  obtain ⟨U1, hU1, U2, hU2, hsub⟩ := Filter.mem_inf_iff_superset.mp hUinf
  obtain ⟨W1, hW1, hWU1⟩ := Filter.mem_comap.mp hU1
  obtain ⟨W2, hW2, hWU2⟩ := Filter.mem_comap.mp hU2
  obtain ⟨m1, hM1⟩ := matrixNeighborhood W1 hW1
  obtain ⟨m2, hM2⟩ := matrixNeighborhood W2 hW2
  let m := max m0 (max 1 (max m1 m2))
  have hm0 : m0 ≤ m := le_max_left _ _
  have hm1 : 1 ≤ m := (le_max_left 1 _).trans (le_max_right _ _)
  have h1 : m1 ≤ m := ((le_max_left m1 m2).trans (le_max_right 1 _)).trans (le_max_right _ _)
  have h2 : m2 ≤ m := ((le_max_right m1 m2).trans (le_max_right 1 _)).trans (le_max_right _ _)
  obtain ⟨Uc, hUc⟩ := exists_congruenceSubgroup v m hm1
  refine ⟨m, hm0, ?_⟩
  intro g hg
  have hgin : g ∈ Uc := (hUc g).mpr hg
  have hginv := (hUc g⁻¹).mp (Uc.inv_mem hgin)
  apply hsub
  exact ⟨hWU1 (hM1 (g : Mat) (matrixMono m1 m h1 (g : Mat) hg)),
    hWU2 (hM2 ((g⁻¹ : GL (Fin 2) K) : Mat)
      (matrixMono m2 m h2 ((g⁻¹ : GL (Fin 2) K) : Mat) hginv))⟩

end ArtinPrimitiveRoots.Proofs.th_cover_sol
