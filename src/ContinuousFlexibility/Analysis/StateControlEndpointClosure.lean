module

public import ContinuousFlexibility.Analysis.ControlCellEndpointBounds
public import ContinuousFlexibility.Analysis.MaterialHeightRegularity
public import ContinuousFlexibility.Analysis.StateControlDecay

/-!
# Smoothness at the endpoints of the controlled profile

The actual control sum has uniform bounds in collars of the two endpoints.
The material height weight tends to zero in both collars, so the control sum
extends smoothly by zero. Applied at a nonzero point of the actual weak
branch, this gives the smooth profile needed for the geometric core.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped ContDiff Topology

/-- Bounds on control jets in arbitrarily small collars suffice for flat extension. -/
theorem contDiff_stateProfile_of_endpoint_control_jet_bounds
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} (hT : IsMaterialData D T) (hD : RadialProfileGeometry D)
    (hχ : ContDiff ℝ ∞ D.chi) (hC : controlGeometryConditions D S C) (x : AnnularState S)
    {γ : ℝ} (hγ : 0 < γ)
    (hbound : ∀ n : ℕ, ∃ δ K : ℝ, 0 < δ ∧ 0 ≤ K ∧ ∀ m r,
      r ∈ Ioo D.a D.b → r ∈ Ioo (C.left m) (C.right m) → endpointDistance D r < δ →
      |stateKappa S x m * iteratedDeriv n (C.control m) r| ≤ K * T.H r ^ γ) :
    ContDiff ℝ ∞ (stateProfile D S C x) := by
  obtain ⟨_, hpos, _, _, _, _, _, _, _, _, _, _, hdecay, _⟩ := hT
  have hlimit (n : ℕ) {l : Filter ℝ}
      (hcore : ∀ᶠ r in l, r ∈ Ioo D.a D.b)
      (hnear : ∀ δ : ℝ, 0 < δ → ∀ᶠ r in l, endpointDistance D r < δ)
      (hend : Tendsto (fun r => T.H r ^ γ) l (𝓝 0)) :
      Tendsto (iteratedDeriv n (stateControlSum C x)) l (𝓝 0) := by
    obtain ⟨δ, K, hδ, hK, hterm⟩ := hbound n
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
      (g := fun r => K * T.H r ^ γ)
    · filter_upwards [hcore, hnear δ hδ] with r hr hrnear
      exact abs_iteratedDeriv_stateControlSum_le hC x n hr
        (mul_nonneg hK (Real.rpow_pos_of_pos (hpos r hr).2.1 _).le)
        (fun m hm => hterm m r hr hm hrnear)
    · simpa only [mul_zero] using hend.const_mul K
  apply contDiff_stateProfile_of_flat_control_sum hD hχ hC x
  · intro n
    have hcore : ∀ᶠ r in 𝓝[>] D.a, r ∈ Ioo D.a D.b := by
      filter_upwards [eventually_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds hD.2.1)] with r ha hb
      exact ⟨ha, hb⟩
    refine hlimit n hcore (fun δ hδ => ?_) ?_
    · have ha : D.a < D.a + δ := by linarith only [hδ]
      filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ha)] with r hr
      have hlt : r < D.a + δ := hr
      exact (min_le_left _ _).trans_lt (by linarith only [hlt])
    · simpa only [Real.rpow_zero, mul_one] using (hdecay 0 γ hγ).choose_spec.2.2.1
  · intro n
    have hcore : ∀ᶠ r in 𝓝[<] D.b, r ∈ Ioo D.a D.b := by
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hD.2.1),
        eventually_mem_nhdsWithin] with r ha hb
      exact ⟨ha, hb⟩
    refine hlimit n hcore (fun δ hδ => ?_) ?_
    · have hb : D.b - δ < D.b := by linarith only [hδ]
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hb)] with r hr
      have hlt : D.b - δ < r := hr
      exact (min_le_right _ _).trans_lt (by linarith only [hlt])
    · simpa only [Real.rpow_zero, mul_one] using (hdecay 0 γ hγ).choose_spec.2.2.2

/-- The specified control cells and the material spaces give a globally smooth actual profile. -/
theorem contDiff_stateProfile_of_controlCellLocations
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}
    (hS : IsPhysicalSpaces D T S) (hT : IsMaterialData D T)
    (hN : N01Properties D T S C base loss ε)
    (hloc : ∀ m r, r ∈ Ioo (C.left m) (C.right m) → r ∈ D.cells (C.cell m))
    (x : AnnularState S) : ContDiff ℝ ∞ (stateProfile D S C x) := by
  have hRef : IsRadialReference D := hN.1
  have hborder : RadialTrueBorder D := hRef.2.2.2.1
  have hgeom : RadialProfileGeometry D := by
    obtain ⟨_, hbounds⟩ := hRef.1
    exact hbounds.1
  have hC : controlGeometryConditions D S C := hN.2.2.2.1
  exact contDiff_stateProfile_of_endpoint_control_jet_bounds hT hgeom hborder.1 hC x
    (γ := ((3 / 4 : ℝ) / 16)) (by norm_num)
    (stateKappa_controlJet_endpoint_bound hS hT hRef.1 hN hloc x)

/-- The core uses the profile and decoded height of the same actual branch state. -/
theorem IsWeakBranch.nonempty_flatAnnularCore_at_of_controlCellLocations
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base loss : ℕ} {ε : ℝ} {B : WeakBranchData S}
    (hB : IsWeakBranch D S C R base ε B) (hN : N01Properties D T S C base loss ε)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hloc : ∀ m r, r ∈ Ioo (C.left m) (C.right m) → r ∈ D.cells (C.cell m))
    {q : ℝ} (hq : |q| < B.radius) (hq₀ : q ≠ 0) : Nonempty FlatAnnularCore :=
  hB.nonempty_flatAnnularCore_of_profile_smooth hN hT hS hq hq₀
    (contDiff_stateProfile_of_controlCellLocations hS hT hN hloc (B.state q))

theorem IsWeakBranch.nonempty_flatAnnularCore_of_controlCellLocations
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {base loss : ℕ} {ε : ℝ} {B : WeakBranchData S}
    (hB : IsWeakBranch D S C R base ε B) (hN : N01Properties D T S C base loss ε)
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hloc : ∀ m r, r ∈ Ioo (C.left m) (C.right m) → r ∈ D.cells (C.cell m)) :
    Nonempty FlatAnnularCore := by
  have hq₀ : 0 < B.radius / 2 := half_pos hB.1
  have hq : |B.radius / 2| < B.radius := by rw [abs_of_pos hq₀]; exact half_lt_self hB.1
  exact hB.nonempty_flatAnnularCore_at_of_controlCellLocations hN hT hS hloc hq hq₀.ne'

end ContinuousFlexibility.Statements
