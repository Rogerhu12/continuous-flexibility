import ContinuousFlexibility.Analysis.ReferenceInverseProfileMaterialJets
import ContinuousFlexibility.Radial.ReferenceModerateCoefficients
import Mathlib.Topology.Order.Compact

/-!
# Physical factors of the same positive reference principal fields

The profile and its radial flux have finite jet bounds on the fixed
closed annulus. Only the reciprocal profile uses the actual cell bounds.
The three factors are combined at the unchanged positive midpoint sample,
with any already selected scaled material envelope C0 * E0.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements ContinuousFlexibility.Radial
open scoped BigOperators ContDiff

private theorem referencePrincipal_profile_flux_compact_jets
    {D : ReferenceData} (hD : RadialProfileGeometry D) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k, k ≤ N → ∀ r ∈ Icc D.a D.b,
      |iteratedDeriv k D.w r| ≤ K ∧
      |iteratedDeriv k (fun x => deriv D.w x / x) r| ≤ K := by
  classical
  let f : Bool → ℝ → ℝ := fun side => if side then
    (fun x => deriv D.w x / x) else D.w
  have hf (side : Bool) : ContDiffOn ℝ ∞ (f side) (Ioi (0 : ℝ)) := by
    cases side with
    | false => exact hD.2.2.1.1.contDiffOn
    | true =>
        exact (contDiff_infty_iff_deriv.mp hD.2.2.1.1).2.contDiffOn.div
          contDiffOn_id (fun x hx => (show 0 < x from hx).ne')
  have hsub : Icc D.a D.b ⊆ Ioi (0 : ℝ) := fun r hr => hD.1.trans_le hr.1
  have hbound (t : Bool × Fin (N + 1)) :
      ∃ A : ℝ, ∀ r ∈ Icc D.a D.b, ‖iteratedDeriv t.2.val (f t.1) r‖ ≤ A :=
    isCompact_Icc.exists_bound_of_continuousOn
      ((reference_contDiffOn_iteratedDeriv isOpen_Ioi (hf t.1) t.2.val).continuousOn.mono hsub)
  choose A hA using hbound
  let K : ℝ := ∑ t : Bool × Fin (N + 1), |A t|
  have hK : 0 ≤ K := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hj (side : Bool) (k : ℕ) (hk : k ≤ N) (r : ℝ) (hr : r ∈ Icc D.a D.b) :
      |iteratedDeriv k (f side) r| ≤ K := by
    let t : Bool × Fin (N + 1) := (side, ⟨k, by omega⟩)
    have hjet : |iteratedDeriv k (f side) r| ≤ A t := by
      simpa only [Real.norm_eq_abs] using hA t r hr
    exact (hjet.trans (le_abs_self _)).trans
      (Finset.single_le_sum (fun _ _ => abs_nonneg _) (Finset.mem_univ t))
  exact ⟨K, hK, fun k hk r hr => ⟨hj false k hk r hr, hj true k hk r hr⟩⟩

/-- Three genuine physical factors have a common finite-prefix envelope
at the original midpoint sample. The supplied C0 and its floor are kept. -/
theorem retainedReference_positive_principal_physical_material_jets
    {S₀ : SelectedTailData} {K₀ : SeedCentralCutoff} {q length : ℝ}
    (P : SeedRetainedPair S₀ K₀ q length) (hSelected : IsSelectedTail S₀)
    (hband : radialFrequencyBand S₀.chain S₀.Cstar S₀.chain.index 2) (hq : 0 < q)
    {Γ : ConnectedReferenceGeometry} (hΓ : Γ.Realizes)
    (hw : Γ.reference.w = P.pair.profile)
    (hcoordinates : R11aRetainedCoordinates P Γ)
    {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
    (hC : controlGeometryConditions Γ.reference S C)
    {T : MaterialData} (hT : IsMaterialData Γ.reference T)
    {C0 : ℝ} (hC0 : 1 ≤ C0) (hfloor : ∀ j, 1 ≤ C0 * T.E0 (T.sample j)) (N : ℕ) :
    ∃ M : ℝ, 1 ≤ M ∧
      ∀ (i : N04PositiveComponent Γ.reference.a Γ.reference.b (deriv Γ.reference.w))
        (j : ℕ), n04PositiveMidpoint i ∈ Γ.reference.cells j →
      ∀ r ∈ Icc (n04PositiveLeft i) (n04PositiveRight i), ∀ k, k ≤ N →
        |iteratedDeriv k Γ.reference.w r| ≤ M * (C0 * T.E0 (T.sample j)) ^ M ∧
        |iteratedDeriv k (fun x => (Γ.reference.w x)⁻¹) r| ≤
          M * (C0 * T.E0 (T.sample j)) ^ M ∧
        |iteratedDeriv k (fun x => deriv Γ.reference.w x / x) r| ≤
          M * (C0 * T.E0 (T.sample j)) ^ M := by
  have hD : RadialProfileGeometry Γ.reference := hΓ.2.1.choose_spec.1
  obtain ⟨P0, hP0, hcompact⟩ := referencePrincipal_profile_flux_compact_jets hD N
  obtain ⟨K, A, hK, hA, hinverse⟩ :=
    retainedReference_positive_inverseProfile_finite_sample_jets
      P hSelected hband hq hΓ hw hcoordinates hC hT N
  let M : ℝ := 1 + P0 + K + A
  have hM : 1 ≤ M := by dsimp only [M]; linarith only [hP0, hK, hA]
  have hP0M : P0 ≤ M := by dsimp only [M]; linarith only [hK, hA]
  have hKM : K ≤ M := by dsimp only [M]; linarith only [hP0, hA]
  have hAM : A ≤ M := by dsimp only [M]; linarith only [hP0, hK]
  refine ⟨M, hM, ?_⟩
  intro i j hmid r hr k hk
  let W : ℝ := C0 * T.E0 (T.sample j)
  have hW : 1 ≤ W := hfloor j
  have hEpos : 0 < T.E0 (T.sample j) :=
    (hT.2.1 _ (materialSample_mem_interval hΓ.2.1 hT j)).2.2.1
  have hEW : T.E0 (T.sample j) ≤ W := le_mul_of_one_le_left hEpos.le hC0
  have hconstant : P0 ≤ M * W ^ M := hP0M.trans
    (le_mul_of_one_le_right (zero_le_one.trans hM)
      (Real.one_le_rpow hW (zero_le_one.trans hM)))
  have hcost : K * T.E0 (T.sample j) ^ A ≤ M * W ^ M := by
    calc
      _ ≤ K * W ^ A := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hEpos.le hEW hA) hK.le
      _ ≤ K * W ^ M := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hW hAM) hK.le
      _ ≤ M * W ^ M := mul_le_mul_of_nonneg_right hKM
        (Real.rpow_nonneg (zero_le_one.trans hW) _)
  have hi := n04PositiveComponent_bounds (hD.2.2.1.1.continuous_deriv (by simp)) i
  have hrD : r ∈ Icc Γ.reference.a Γ.reference.b :=
    ⟨hi.1.trans hr.1, hr.2.trans hi.2.2⟩
  exact ⟨((hcompact k hk r hrD).1).trans hconstant,
    (hinverse i j hmid r hr k hk).trans hcost,
    ((hcompact k hk r hrD).2).trans hconstant⟩

end ContinuousFlexibility.Analysis
