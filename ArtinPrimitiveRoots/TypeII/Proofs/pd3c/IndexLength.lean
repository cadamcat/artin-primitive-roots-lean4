import ArtinPrimitiveRoots.TypeII.PD.Memory
set_option autoImplicit false
open Classical
namespace ArtinPrimitiveRoots.TypeII.PD

example {x : ℝ} {K : ℕ} (l : List Particle) (D : Finset (Fin l.length)) :
    (removeIndices l D).length = l.length - D.card := by
  classical
  unfold removeIndices
  rw [List.length_filterMap_eq_countP]
  have hp : (fun a : Fin l.length => (if a ∈ D then none else some (l.get a)).isSome) =
      fun a => a ∉ D := by
    funext a
    by_cases h : a ∈ D <;> simp [h]
  rw [hp]
  have hfin : (List.finRange l.length).toFinset = (Finset.univ : Finset (Fin l.length)) := by
    ext a
    simp
  have hcount :
      (List.finRange l.length).countP (fun a => a ∉ D) =
        ((List.finRange l.length).toFinset.filter (fun a => a ∉ D)).card :=
    (List.nodup_finRange _).card_eq_countP.symm
  rw [hcount, hfin]
  have hfilter : (Finset.univ : Finset (Fin l.length)).filter (fun a => a ∉ D) =
      Finset.univ \ D := by
    ext a
    simp
  rw [hfilter, Finset.card_sdiff_of_subset (Finset.subset_univ D)]
  simp

end ArtinPrimitiveRoots.TypeII.PD
