module

public import ContinuousFlexibility.Analysis.N06TurningRootFiniteness

/-!
# Compact sets meet only finitely many natural sign intervals

Distinct sign intervals have distinct left roots. On a compact interior
window these roots are finite, and at most one interval can enter the
window from its left. This applies to the actual negative components
retained in N01's control geometry, including their endpoints.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set

theorem n06_disjoint_intervals_left_injective {ι : Type*} {l r : ι → ℝ}
    (hlr : ∀ i, l i < r i)
    (hdisjoint : Pairwise (fun i j => Disjoint (Ioo (l i) (r i)) (Ioo (l j) (r j)))) :
    Function.Injective l := by
  intro i j hij
  by_contra hne
  have hsmall : l i < min (r i) (r j) := lt_min (hlr i) (hij ▸ hlr j)
  obtain ⟨x, hx, hxmin⟩ := exists_between hsmall
  apply (Set.disjoint_left.mp (hdisjoint hne))
    (show x ∈ Ioo (l i) (r i) from ⟨hx, hxmin.trans_le (min_le_left _ _)⟩)
  exact ⟨hij ▸ hx, hxmin.trans_le (min_le_right _ _)⟩

theorem n06_finite_root_intervals_meeting_compact {ι : Type*} {a b : ℝ}
    {l r : ι → ℝ} {f : ℝ → ℝ}
    (hlr : ∀ i, l i < r i)
    (hdisjoint : Pairwise (fun i j => Disjoint (Ioo (l i) (r i)) (Ioo (l j) (r j))))
    (hzero : ∀ i, f (l i) = 0)
    (hroots : ∀ J : Set ℝ, IsCompact J → J ⊆ Ioo a b →
      {x | x ∈ J ∧ f x = 0}.Finite)
    {J : Set ℝ} (hJ : IsCompact J) (hJD : J ⊆ Ioo a b) :
    {i | (Icc (l i) (r i) ∩ J).Nonempty}.Finite := by
  classical
  by_cases hne : J.Nonempty
  · obtain ⟨u, hu⟩ := hJ.exists_isLeast hne
    obtain ⟨v, hv⟩ := hJ.exists_isGreatest hne
    let a' : ℝ := (a + u) / 2
    let b' : ℝ := (v + b) / 2
    have ha' : a < a' ∧ a' < u := by
      have ha := (hJD hu.1).1
      dsimp only [a']
      constructor <;> linarith
    have hb' : v < b' ∧ b' < b := by
      have hb := (hJD hv.1).2
      dsimp only [b']
      constructor <;> linarith
    have hwindow : Icc a' b' ⊆ Ioo a b := fun x hx =>
      ⟨ha'.1.trans_le hx.1, hx.2.trans_lt hb'.2⟩
    have hfinite := hroots (Icc a' b') isCompact_Icc hwindow
    have hinj := n06_disjoint_intervals_left_injective hlr hdisjoint
    have hleft : {i | l i ∈ Icc a' b'}.Finite := by
      apply (hfinite.preimage hinj.injOn).subset
      intro i hi
      exact ⟨hi, hzero i⟩
    have hcross : {i | l i < a' ∧ a' < r i}.Subsingleton := by
      intro i hi j hj
      by_contra hij
      exact (Set.disjoint_left.mp (hdisjoint hij)) hi hj
    apply (hleft.union hcross.finite).subset
    intro i hi
    obtain ⟨x, hxi, hxJ⟩ := hi
    by_cases hli : a' ≤ l i
    · exact Or.inl ⟨hli, hxi.1.trans ((hv.2 hxJ).trans hb'.1.le)⟩
    · exact Or.inr ⟨lt_of_not_ge hli, (ha'.2.trans_le (hu.2 hxJ)).trans_le hxi.2⟩
  · have hJempty : J = ∅ := not_nonempty_iff_eq_empty.mp hne
    simp only [hJempty, inter_empty, Set.not_nonempty_empty, Set.ofPred_false, finite_empty]

/-- The actual N01 negative components, with their closures, are locally
finite in the form needed for every compactly supported physical test. -/
theorem n06_controlComponents_finite_on_compact {D : ReferenceData}
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hD : RadialProfileGeometry D) (hC : controlGeometryConditions D S C)
    {J : Set ℝ} (hJ : IsCompact J) (hJD : J ⊆ radialCore D) :
    {m | (Icc (C.left m) (C.right m) ∩ J).Nonempty}.Finite := by
  apply n06_finite_root_intervals_meeting_compact
    (fun m => (hC.1 m).2.1) (fun i j hij => hC.2.2.1 i j hij)
    (fun m => (hC.2.1 m).1)
    (fun J hJ hJD => n06_turningRoots_finite_on_compact hD hJ hJD) hJ hJD

end ContinuousFlexibility.Statements
