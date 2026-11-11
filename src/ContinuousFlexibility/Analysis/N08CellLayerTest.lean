import ContinuousFlexibility.Analysis.IntervalLayerCutoff
import ContinuousFlexibility.Analysis.SpacesCompactHeights
import ContinuousFlexibility.Radial.ProfileLayerGeometry
import ContinuousFlexibility.Statements.Nonlinear

/-!
# Actual radial tests on a complete reference cell

The endpoint-distance bounds of the reference partition determine one
smooth endpoint band for each cell. Its cutoff is one on a neighborhood
of the entire cell. Multiplying by the radius gives a genuine compact
height whose derivative is one throughout every negative component in
that cell; the derivative is free to change outside the component.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

def n08CellLayerInner (A : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-((n : ℝ) + 1) ^ 2) / (2 * A)

def n08CellLayerOuter (A : ℝ) (n : ℕ) : ℝ :=
  2 * A * Real.exp (-(n : ℝ) ^ 2)

theorem n08CellLayerInner_pos {A : ℝ} (hA : 0 < A) (n : ℕ) :
    0 < n08CellLayerInner A n :=
  div_pos (Real.exp_pos _) (mul_pos (by norm_num) hA)

theorem n08CellLayerOuter_pos {A : ℝ} (hA : 0 < A) (n : ℕ) :
    0 < n08CellLayerOuter A n :=
  mul_pos (mul_pos (by norm_num) hA) (Real.exp_pos _)

theorem n08CellLayerInner_le_one {A : ℝ} (hA : 1 ≤ A) (n : ℕ) :
    n08CellLayerInner A n ≤ 1 := by
  have he : Real.exp (-((n : ℝ) + 1) ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  apply (div_le_iff₀ (by linarith : 0 < 2 * A)).mpr
  dsimp only [n08CellLayerInner]
  linarith

theorem n08CellLayerInner_le_outer {A : ℝ} (hA : 1 ≤ A) (n : ℕ) :
    n08CellLayerInner A n ≤ n08CellLayerOuter A n := by
  have h := Radial.profileLayerLower_le_upper (by linarith : 1 ≤ 2 * A) n
  simpa only [n08CellLayerInner, n08CellLayerOuter, Radial.profileLayerLower,
    Radial.profileLayerUpper, div_eq_mul_inv, mul_comm] using h

/-- A single band constant works for all actual reference cells. -/
theorem n08_referenceCell_layer_parameters {D : ReferenceData}
    (hD : IsAccumulatingProfile D) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ m r, r ∈ D.cells m →
      n08CellLayerInner A (D.cellIndex m) < endpointDistance D r ∧
        endpointDistance D r < n08CellLayerOuter A (D.cellIndex m) := by
  obtain ⟨C, hC⟩ := hD
  have hC0 : 0 < C 0 := hC.2.2.1 0
  have hdist := hC.2.2.2.2.2.2.1
  let A : ℝ := max (C 0) 1
  have hA : 1 ≤ A := le_max_right _ _
  have hCA : C 0 ≤ A := le_max_left _ _
  have hA0 : 0 < A := zero_lt_one.trans_le hA
  refine ⟨A, hA, fun m r hr => ?_⟩
  have hd := hdist m r hr
  have he := Real.exp_pos (-((D.cellIndex m : ℝ) + 1) ^ 2)
  have hlo : Real.exp (-((D.cellIndex m : ℝ) + 1) ^ 2) / A ≤ endpointDistance D r := by
    apply (div_le_div_of_nonneg_left he.le hC0 hCA).trans
    simpa only [endpointDistance, div_eq_mul_inv, mul_comm] using hd.1
  have he' := Real.exp_pos (-(D.cellIndex m : ℝ) ^ 2)
  have hhi : endpointDistance D r ≤ A * Real.exp (-(D.cellIndex m : ℝ) ^ 2) :=
    hd.2.trans (mul_le_mul_of_nonneg_right hCA he'.le)
  constructor
  · have hhalf : n08CellLayerInner A (D.cellIndex m) =
        (Real.exp (-((D.cellIndex m : ℝ) + 1) ^ 2) / A) / 2 := by
      dsimp only [n08CellLayerInner]
      ring
    rw [hhalf]
    exact (half_lt_self (div_pos he hA0)).trans_le hlo
  · dsimp only [n08CellLayerOuter]
    have hp : 0 < A * Real.exp (-(D.cellIndex m : ℝ) ^ 2) := mul_pos hA0 he'
    linarith

def n08CellLayerCutoff (D : ReferenceData) (A : ℝ) (m : ℕ) : ℝ → ℝ :=
  Analysis.intervalLayerCutoff D.a D.b
    (n08CellLayerInner A (D.cellIndex m)) (n08CellLayerOuter A (D.cellIndex m))

theorem n08CellLayerCutoff_contDiff (D : ReferenceData) (A : ℝ) (m : ℕ) :
    ContDiff ℝ ∞ (n08CellLayerCutoff D A m) :=
  Analysis.contDiff_intervalLayerCutoff _ _ _ _

theorem n08CellLayerCutoff_compact {D : ReferenceData} {A : ℝ}
    (hA : 0 < A) (m : ℕ) : HasCompactSupport (n08CellLayerCutoff D A m) :=
  Analysis.hasCompactSupport_intervalLayerCutoff
    (n08CellLayerInner_pos hA _) (n08CellLayerOuter_pos hA _)

theorem n08CellLayerCutoff_tsupport {D : ReferenceData} {A : ℝ}
    (hA : 0 < A) (m : ℕ) :
    tsupport (n08CellLayerCutoff D A m) ⊆
      Analysis.intervalEndpointLayer D.a D.b
        (n08CellLayerInner A (D.cellIndex m)) (n08CellLayerOuter A (D.cellIndex m)) :=
  Analysis.tsupport_intervalLayerCutoff_subset
    (n08CellLayerInner_pos hA _) (n08CellLayerOuter_pos hA _)

theorem n08CellLayerCutoff_tsupport_core {D : ReferenceData} {A : ℝ}
    (hA : 0 < A) (m : ℕ) :
    tsupport (n08CellLayerCutoff D A m) ⊆ Ioo D.a D.b :=
  (n08CellLayerCutoff_tsupport hA m).trans
    (Analysis.intervalEndpointLayer_subset_Ioo (n08CellLayerInner_pos hA _))

theorem n08CellLayerCutoff_eventually_one {D : ReferenceData} {A r : ℝ}
    (hA : 0 < A) (m : ℕ)
    (hr : n08CellLayerInner A (D.cellIndex m) < endpointDistance D r ∧
      endpointDistance D r < n08CellLayerOuter A (D.cellIndex m)) :
    n08CellLayerCutoff D A m =ᶠ[𝓝 r] (fun _ => (1 : ℝ)) := by
  have hnear := ((Analysis.continuous_intervalEndpointDistance D.a D.b).continuousAt).preimage_mem_nhds
    (Ioo_mem_nhds hr.1 hr.2)
  filter_upwards [hnear] with x hx
  exact Analysis.intervalLayerCutoff_one (n08CellLayerInner_pos hA _)
    (n08CellLayerOuter_pos hA _) hx.1.le hx.2.le

def n08CellLayerProfile (D : ReferenceData) (A : ℝ) (m : ℕ) (r : ℝ) : ℝ :=
  r * n08CellLayerCutoff D A m r

theorem n08CellLayerProfile_contDiff (D : ReferenceData) (A : ℝ) (m : ℕ) :
    ContDiff ℝ ∞ (n08CellLayerProfile D A m) :=
  contDiff_id.mul (n08CellLayerCutoff_contDiff D A m)

theorem n08CellLayerProfile_hasDerivAt {D : ReferenceData} {A r : ℝ}
    (hA : 0 < A) (m : ℕ)
    (hr : n08CellLayerInner A (D.cellIndex m) < endpointDistance D r ∧
      endpointDistance D r < n08CellLayerOuter A (D.cellIndex m)) :
    HasDerivAt (n08CellLayerProfile D A m) 1 r := by
  apply (hasDerivAt_id r).congr_of_eventuallyEq
  filter_upwards [n08CellLayerCutoff_eventually_one hA m hr] with x hx
  change x * n08CellLayerCutoff D A m x = x
  rw [hx, mul_one]

theorem n08CellLayerProfile_heightMember {D : ReferenceData} {T : MaterialData}
    (hT : IsMaterialData D T) {A : ℝ} (hA : 0 < A) (m : ℕ) (γ : ℝ) :
    HeightMember D T γ (fun p : PolarPoint => n08CellLayerProfile D A m p.1) := by
  apply spaces_heightMember_of_compact_radial hT (n08CellLayerProfile_contDiff D A m)
    (n08CellLayerCutoff_compact hA m) (n08CellLayerCutoff_tsupport_core hA m)
  intro r hr
  have hz : n08CellLayerCutoff D A m r = 0 := by
    by_contra hn
    exact hr (subset_closure hn)
  change r * n08CellLayerCutoff D A m r = 0
  rw [hz, mul_zero]

def n08CellLayerHeight {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {A : ℝ} (hA : 0 < A) (m : ℕ) (γ : ℝ) : (S.height γ).Space :=
  Classical.choose ((hS.1 γ).2.2.2.2.1 _ (n08CellLayerProfile_heightMember hT hA m γ))

theorem n08CellLayerHeight_decode {D : ReferenceData} {T : MaterialData}
    {S : PhysicalSpacesData} (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    {A : ℝ} (hA : 0 < A) (m : ℕ) (γ : ℝ) :
    (S.height γ).decode (n08CellLayerHeight hT hS hA m γ) =
      fun p : PolarPoint => n08CellLayerProfile D A m p.1 :=
  Classical.choose_spec ((hS.1 γ).2.2.2.2.1 _ (n08CellLayerProfile_heightMember hT hA m γ))

end ContinuousFlexibility.Statements
