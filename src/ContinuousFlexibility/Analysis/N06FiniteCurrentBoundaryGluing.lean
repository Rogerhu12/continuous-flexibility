import ContinuousFlexibility.Analysis.N06FiniteAtlasBoundary
import ContinuousFlexibility.Analysis.N06CurrentBoundaryTestSupport
import ContinuousFlexibility.Analysis.N06CutBoundaryIntegral
import ContinuousFlexibility.Analysis.N06BoundaryRadialOrientation

/-!
# Actual canonical endpoint rows on the finite physical atlas

Each canonical Green row is assigned to its actual physical endpoint,
with the sign of the radial orientation. This includes an increasing
positive or negative chart and a decreasing negative half-chart in the
same formula. The original test support removes all exterior endpoints.
The actual a.e. cover supplies the unique neighboring piece at every
interior endpoint, so the explicit two-sided density identities cancel
the complete finite sum.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

/-- A compact radial support admits a strictly larger closed window
inside the original annulus, including when that support is empty. -/
theorem n06_compact_openInterval_window {a b : ℝ} (hab : a < b)
    {J : Set ℝ} (hJ : IsCompact J) (hJsub : J ⊆ Ioo a b) :
    ∃ l r : ℝ, l < r ∧ J ⊆ Ioo l r ∧ Icc l r ⊆ Ioo a b := by
  by_cases hne : J.Nonempty
  · obtain ⟨c, hc⟩ := hJ.exists_isLeast hne
    obtain ⟨d, hd⟩ := hJ.exists_isGreatest hne
    obtain ⟨l, hal, hlc⟩ := exists_between (hJsub hc.1).1
    obtain ⟨r, hdr, hrb⟩ := exists_between (hJsub hd.1).2
    exact ⟨l, r, (hlc.trans_le (hc.2 hd.1)).trans hdr,
      fun x hx => ⟨hlc.trans_le (hc.2 hx), (hd.2 hx).trans_lt hdr⟩,
      fun x hx => ⟨hal.trans_le hx.1, hx.2.trans_lt hrb⟩⟩
  · obtain ⟨l, hal, hlb⟩ := exists_between hab
    obtain ⟨r, hlr, hrb⟩ := exists_between hlb
    exact ⟨l, r, hlr, fun x hx => (hne ⟨x, hx⟩).elim,
      fun x hx => ⟨hal.trans_le hx.1, hx.2.trans_lt hrb⟩⟩

/-- The physical-side endpoint row. The reversal flag only records
which of the two canonical endpoints is the actual forward image. -/
def n06OrientedCanonicalBoundary
    {S : PhysicalSpacesData} {K : CanonicalData S} {z : AnnularState S × ℝ}
    {m : ℕ} {φ : PolarPoint → ℝ}
    (Q : N06CurrentHeightTestTraces S K z m φ) (W : PolarPoint → ℝ)
    (a : ℝ → ℝ) (reverse physicalUpper : Bool) (θ : ℝ) : ℝ :=
  let y := n06Endpoint (K.left m) (K.right m)
    (if reverse then !physicalUpper else physicalUpper)
  (if reverse then (-1 : ℝ) else 1) * a y *
    (Q.value (y, θ) * radialPartial W (y, θ) - W (y, θ) * Q.radial (y, θ))

/-- Reversing a chart exchanges the two canonical endpoints and reverses
both physical normal rows, leaving the same canonical Green difference. -/
theorem n06_orientedCanonicalBoundary_difference
    {S : PhysicalSpacesData} {K : CanonicalData S} {z : AnnularState S × ℝ}
    {m : ℕ} {φ W : PolarPoint → ℝ}
    (Q : N06CurrentHeightTestTraces S K z m φ) (a : ℝ → ℝ)
    (hW : ContDiff ℝ 1 W) (reverse : Bool) :
    ((∫ θ in (0 : ℝ)..Real.pi, n06OrientedCanonicalBoundary Q W a reverse true θ) -
      ∫ θ in (0 : ℝ)..Real.pi, n06OrientedCanonicalBoundary Q W a reverse false θ) =
      ∫ θ in (0 : ℝ)..Real.pi,
        a (K.right m) * (Q.value (K.right m, θ) * radialPartial W (K.right m, θ) -
          W (K.right m, θ) * Q.radial (K.right m, θ)) -
        a (K.left m) * (Q.value (K.left m, θ) * radialPartial W (K.left m, θ) -
          W (K.left m, θ) * Q.radial (K.left m, θ)) := by
  have hright : IntervalIntegrable (fun θ => a (K.right m) *
      (Q.value (K.right m, θ) * radialPartial W (K.right m, θ) -
        W (K.right m, θ) * Q.radial (K.right m, θ))) volume 0 Real.pi :=
    ((n06_current_boundary_wronskian_continuous Q hW (K.right m)).const_mul _).intervalIntegrable _ _
  have hleft : IntervalIntegrable (fun θ => a (K.left m) *
      (Q.value (K.left m, θ) * radialPartial W (K.left m, θ) -
        W (K.left m, θ) * Q.radial (K.left m, θ))) volume 0 Real.pi :=
    ((n06_current_boundary_wronskian_continuous Q hW (K.left m)).const_mul _).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hright hleft]
  cases reverse <;>
    simp only [n06OrientedCanonicalBoundary, n06Endpoint, Bool.false_eq_true, if_false,
      if_true, Bool.not_false, Bool.not_true, one_mul, neg_one_mul, neg_mul,
      intervalIntegral.integral_neg]
  ring

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}
  {φ : PolarPoint → ℝ}

/-- The original physical test itself supplies a compact support and an
interior window; no support window is an additional test requirement. -/
theorem n06_radialTest_supportWindow
    (hD : IsAccumulatingProfile D) (hφ : RadialTest D φ) :
    ∃ J : Set ℝ, ∃ l r : ℝ, IsCompact J ∧ l < r ∧ J ⊆ Ioo l r ∧
      Icc l r ⊆ radialCore D ∧ (∀ x, x ∉ J → ∀ θ, φ (x, θ) = 0) := by
  obtain ⟨J, hJ, hJD, hzero⟩ := hφ.2.2
  obtain ⟨l, r, hlr, hsub, hwindow⟩ :=
    n06_compact_openInterval_window hD.choose_spec.1.2.1 hJ hJD
  exact ⟨J, l, r, hJ, hlr, hsub, hwindow, hzero⟩

/-- One genuine forward endpoint record, together with the original test
support, removes its entire oriented boundary integral. -/
theorem n06_orientedCanonicalBoundary_zero_off_support
    {m : ℕ} (Q : N06CurrentHeightTestTraces S K z m φ)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (W : PolarPoint → ℝ) (a : ℝ → ℝ) (reverse physicalUpper : Bool)
    {σ : ℝ} {β H ρ κ Hr : ℝ → ℝ}
    (Jroot : N06RootFirstJets (K.chart z m) (K.height z m)
      (n06Endpoint (K.physicalLeft m) (K.physicalRight m) physicalUpper)
      (n06Endpoint (K.left m) (K.right m)
        (if reverse then !physicalUpper else physicalUpper)) σ β H ρ κ Hr)
    {J : Set ℝ} (hJ : IsClosed J)
    (hzero : ∀ x, x ∉ J → ∀ θ, φ (x, θ) = 0)
    (hout : n06Endpoint (K.physicalLeft m) (K.physicalRight m) physicalUpper ∉ J) :
    (∫ θ in (0 : ℝ)..Real.pi,
      n06OrientedCanonicalBoundary Q W a reverse physicalUpper θ) = 0 := by
  have hr : n06Endpoint (K.physicalLeft m) (K.physicalRight m) physicalUpper ∈
      Icc (K.physicalLeft m) (K.physicalRight m) := by
    cases physicalUpper <;> simp only [n06Endpoint, Bool.false_eq_true, if_false, if_true,
      mem_Icc, le_refl, true_and, and_true] <;> exact (h04.2.2.2.1 m).1.le
  calc
    _ = ∫ _θ in (0 : ℝ)..Real.pi, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      have hθ' : θ ∈ Icc (0 : ℝ) Real.pi :=
        by simpa only [uIcc_of_le Real.pi_pos.le] using hθ
      obtain ⟨hv, hd, _⟩ := Q.boundary_zero_off_support h04 hz hs Jroot hr hJ hzero hout hθ'
      simp only [n06OrientedCanonicalBoundary, hv, hd, zero_mul, mul_zero, sub_self]
    _ = 0 := by simp

/-- The real endpoint rows cancel on the actual finite atlas. Only the
two-sided pointwise density identity is supplied; existence and uniqueness
of neighbors, finiteness, and all exterior zero terms are derived. -/
theorem n06_current_finiteAtlas_boundary_sum
    (hD : IsAccumulatingProfile D)
    (hcoords : N05ControlledReferenceCoordinates D S C K)
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    {J : Set ℝ} (hJ : IsClosed J) {l r : ℝ}
    (hJwindow : J ⊆ Ioo l r) (hwindow : Icc l r ⊆ radialCore D)
    (hsupport : ∀ x, x ∉ J → ∀ θ, φ (x, θ) = 0)
    (Q : ∀ m, N06CurrentHeightTestTraces S K z m φ)
    (W : ℕ → PolarPoint → ℝ) (a : ℕ → ℝ → ℝ) (reverse : ℕ → Bool)
    (hends : ∀ m, ∀ side : Bool, ∃ σ : ℝ, ∃ β H ρ κ Hr : ℝ → ℝ,
      Nonempty (N06RootFirstJets (K.chart z m) (K.height z m)
        (n06Endpoint (K.physicalLeft m) (K.physicalRight m) side)
        (n06Endpoint (K.left m) (K.right m) (if reverse m then !side else side))
          σ β H ρ κ Hr))
    (hmatch : ∀ i j, K.physicalRight i = K.physicalLeft j →
      ∀ θ ∈ Icc (0 : ℝ) Real.pi,
        n06OrientedCanonicalBoundary (Q i) (W i) (a i) (reverse i) true θ =
          n06OrientedCanonicalBoundary (Q j) (W j) (a j) (reverse j) false θ) :
    ∃ hfinite : {m : ℕ |
        (Ioo (K.physicalLeft m) (K.physicalRight m) ∩ Icc l r).Nonempty}.Finite,
      (∑ m ∈ hfinite.toFinset,
        ((∫ θ in (0 : ℝ)..Real.pi,
          n06OrientedCanonicalBoundary (Q m) (W m) (a m) (reverse m) true θ) -
        ∫ θ in (0 : ℝ)..Real.pi,
          n06OrientedCanonicalBoundary (Q m) (W m) (a m) (reverse m) false θ)) = 0 := by
  classical
  have hfinite := n06_controlledReferencePieces_finite_on_compact hD hcoords isCompact_Icc hwindow
  have houter (m : ℕ) (side : Bool)
      (hout : n06Endpoint (K.physicalLeft m) (K.physicalRight m) side ∉ Ioo l r) :
      (∫ θ in (0 : ℝ)..Real.pi,
        n06OrientedCanonicalBoundary (Q m) (W m) (a m) (reverse m) side θ) = 0 := by
    obtain ⟨σ, β, H, ρ, κ, Hr, ⟨Jroot⟩⟩ := hends m side
    apply n06_orientedCanonicalBoundary_zero_off_support (Q m) h04 hz hs
      (W m) (a m) (reverse m) side Jroot hJ hsupport
    exact fun hm => hout (hJwindow hm)
  refine ⟨hfinite, n06_finitePhysicalWindow_boundary_sum h04 hwindow hfinite
    (fun m => ∫ θ in (0 : ℝ)..Real.pi,
      n06OrientedCanonicalBoundary (Q m) (W m) (a m) (reverse m) false θ)
    (fun m => ∫ θ in (0 : ℝ)..Real.pi,
      n06OrientedCanonicalBoundary (Q m) (W m) (a m) (reverse m) true θ) ?_ ?_ ?_⟩
  · intro i _ j _ hij
    apply intervalIntegral.integral_congr
    intro θ hθ
    exact hmatch i j hij θ (by simpa only [uIcc_of_le Real.pi_pos.le] using hθ)
  · intro m _ hout
    exact houter m false hout
  · intro m _ hout
    exact houter m true hout

end ContinuousFlexibility.Statements
