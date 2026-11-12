import ContinuousFlexibility.Analysis.CanonicalActualEndpointFields
import ContinuousFlexibility.Analysis.PlanarInverseDerivativeBound

/-!
# Quantitative diagonal bounds at actual fixed root circles

The actual inverse derivative is a left inverse. Since the root circle
is fixed, the forward derivative is triangular there. A norm bound on
the inverse therefore bounds both positive diagonal entries from below.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped Topology ContDiff

private theorem root_triangular_diagonal_lower
    (A B : PolarPoint →L[ℝ] PolarPoint) {M : ℝ} (hM : 0 < M)
    (hleft : B.comp A = ContinuousLinearMap.id ℝ PolarPoint)
    (hzero : (A (0, 1)).1 = 0)
    (ha : 0 < (A (1, 0)).1) (hd : 0 < (A (0, 1)).2) (hB : ‖B‖ ≤ M) :
    M⁻¹ ≤ (A (1, 0)).1 ∧ M⁻¹ ≤ (A (0, 1)).2 := by
  have h1 := congrArg (fun L : PolarPoint →L[ℝ] PolarPoint => L (1, 0)) hleft
  have h2 := congrArg (fun L : PolarPoint →L[ℝ] PolarPoint => L (0, 1)) hleft
  change B (A (1, 0)) = (1, 0) at h1
  change B (A (0, 1)) = (0, 1) at h2
  rw [planeCLM_apply_decompose B (A (1, 0))] at h1
  rw [planeCLM_apply_decompose B (A (0, 1))] at h2
  have h12 : (A (0, 1)).2 * (B (0, 1)).1 = 0 := by
    simpa only [hzero, zero_mul, zero_add] using congrArg Prod.fst h2
  have hB12 : (B (0, 1)).1 = 0 := (mul_eq_zero.mp h12).resolve_left hd.ne'
  have h11 : (A (1, 0)).1 * (B (1, 0)).1 = 1 := by
    simpa only [hB12, mul_zero, add_zero] using congrArg Prod.fst h1
  have h22 : (A (0, 1)).2 * (B (0, 1)).2 = 1 := by
    simpa only [hzero, zero_mul, zero_add] using congrArg Prod.snd h2
  have hnorm (v : PolarPoint) (hv : ‖v‖ ≤ 1) : ‖B v‖ ≤ M :=
    (B.le_opNorm v).trans ((mul_le_of_le_one_right (norm_nonneg B) hv).trans hB)
  have hb11 : (B (1, 0)).1 ≤ M := by
    calc
      _ ≤ |(B (1, 0)).1| := le_abs_self _
      _ ≤ ‖B (1, 0)‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le (B (1, 0))
      _ ≤ M := hnorm (1, 0) (by norm_num [Prod.norm_def])
  have hb22 : (B (0, 1)).2 ≤ M := by
    calc
      _ ≤ |(B (0, 1)).2| := le_abs_self _
      _ ≤ ‖B (0, 1)‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le (B (0, 1))
      _ ≤ M := hnorm (0, 1) (by norm_num [Prod.norm_def])
  have hlower (a b : ℝ) (ha : 0 < a) (hab : a * b = 1) (hb : b ≤ M) : M⁻¹ ≤ a := by
    apply (inv_le_iff_one_le_mul₀ hM).mpr
    calc
      1 = a * b := hab.symm
      _ ≤ a * M := mul_le_mul_of_nonneg_left hb ha.le
  exact ⟨hlower _ _ ha h11 hb11, hlower _ _ hd h22 hb22⟩

/-- Only a first-derivative bound for the genuine inverse is supplied.
The triangularity, inverse identity and positivity come from actual
Part A and cut geometry, on the same root circle and same state. -/
theorem canonicalCurrentPoint_root_diagonal_lower
    {D : ReferenceData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {K : CanonicalData S} {base : ℕ} {ε : ℝ}
    (hA : CanonicalGeometry D S C K base ε)
    (hcut : CanonicalCutGeometry S C K base ε)
    (href : (C.referenceState, 0) ∈ stateNeighborhood S C base ε)
    (hsref : stateSector S C.referenceState)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (side : Bool) (θ : ℝ)
    {M : ℝ} (hM : 0 < M)
    (hbound :
      let i := if side then (K.cutPair m).2 else (K.cutPair m).1
      let r := n01ComponentRoot C m side
      ‖fderiv ℝ (canonicalReferencePoint C K z i)
        (canonicalCurrentPoint C K z i (r, θ))‖ ≤ M) :
    let i := if side then (K.cutPair m).2 else (K.cutPair m).1
    let r := n01ComponentRoot C m side
    M⁻¹ ≤ radialPartial (fun p => (canonicalCurrentPoint C K z i p).1) (r, θ) ∧
      M⁻¹ ≤ angularPartial (fun p => (canonicalCurrentPoint C K z i p).2) (r, θ) := by
  let i := if side then (K.cutPair m).2 else (K.cutPair m).1
  let r := n01ComponentRoot C m side
  let F : PolarPoint → PolarPoint := canonicalCurrentPoint C K z i
  let G : PolarPoint → PolarPoint := canonicalReferencePoint C K z i
  have hclosed : (r, θ) ∈ physicalPieceClosed S K (C.referenceState, 0) i :=
    (canonicalCutRoot_mem_closed_and_zero hA hcut href hsref m side θ).1
  have hF : DifferentiableAt ℝ F (r, θ) :=
    (n04Coordinates_currentPoint_contDiffAt_closed hA href hsref hz hs i hclosed).differentiableAt
      (by simp)
  have hG := canonicalCurrentPoint_closed_inverse_data hA href hsref hz hs i hclosed
  have hgerm : G ∘ F =ᶠ[𝓝 (r, θ)] (id : PolarPoint → PolarPoint) := hG.2.1
  have hleft : (fderiv ℝ G (F (r, θ))).comp (fderiv ℝ F (r, θ)) =
      ContinuousLinearMap.id ℝ PolarPoint := by
    rw [← fderiv_comp (r, θ) (hG.1.differentiableAt (by simp)) hF,
      hgerm.fderiv_eq, fderiv_id]
  have he : (fun η => (F (r, η)).1) = (fun _ : ℝ => r) :=
    funext (canonicalCurrentPoint_root_radial hA hcut href hsref hz hs m side)
  have hzpartial := (hasDerivAt_angular_slice hF.fst).deriv
  rw [he, deriv_const] at hzpartial
  have hzero : (fderiv ℝ F (r, θ) (0, 1)).1 = 0 := by
    have hh := hzpartial.symm
    dsimp only [angularPartial] at hh
    rw [(hF.hasFDerivAt.fst).fderiv] at hh
    exact hh
  have hpos := canonicalCurrentPoint_root_positive_diagonal hA hcut href hsref hz hs m side θ
  change 0 < radialPartial (fun p => (F p).1) (r, θ) ∧
    0 < angularPartial (fun p => (F p).2) (r, θ) at hpos
  change M⁻¹ ≤ radialPartial (fun p => (F p).1) (r, θ) ∧
    M⁻¹ ≤ angularPartial (fun p => (F p).2) (r, θ)
  dsimp only [radialPartial, angularPartial] at hpos ⊢
  rw [(hF.hasFDerivAt.fst).fderiv, (hF.hasFDerivAt.snd).fderiv] at hpos ⊢
  exact root_triangular_diagonal_lower _ _ hM hleft hzero hpos.1 hpos.2 hbound

end ContinuousFlexibility.Analysis
