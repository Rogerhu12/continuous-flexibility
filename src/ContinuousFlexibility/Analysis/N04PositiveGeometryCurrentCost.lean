import ContinuousFlexibility.Analysis.N04PositiveGeometryInverseBoundary
import ContinuousFlexibility.Analysis.N04PositiveGeometryCircleVariation
import ContinuousFlexibility.Analysis.N04PositiveGeometryBufferCost

/-!
# A necessary right-collar cost for the actual current geometry

The order-one spatial estimate for the actual inverse-angle atom forces a
uniform reciprocal-width estimate for every supplied right buffer.  The
test state is a genuine single-component circle direction in the physical
sector.  Its positive amplitude appears both in the prescribed endpoint
jump and in the parameter grading, and therefore cancels.

Only the value-bound clause of the existing `GeometryData` is used.  The
reference inverse-angle atom is identically zero, the middle germ fixes
the current atom to zero, and the original N01 label fixes its right
endpoint value.  Thus this necessary condition does not assume any
additional inverse or transport estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

attribute [local instance]
  n07aNonlinearAnnularGroup n07aNonlinearAnnularModule
  n07aNonlinearAnnularAddGroup n07aNonlinearAnnularSMul n07aNonlinearAnnularSub
  n07aNonlinearAnnularParameterGroup n07aNonlinearAnnularParameterModule
  n07aNonlinearAnnularParameterAddGroup n07aNonlinearAnnularParameterSMul
  n07aNonlinearAnnularParameterSub
  n07aNonlinearDirectionsGroup n07aNonlinearDirectionsModule
  n07aNonlinearDirectionsAddGroup n07aNonlinearDirectionsSMul n07aNonlinearDirectionsSub
  n07aNonlinearSectorParameterGroup n07aNonlinearSectorParameterModule
  n07aNonlinearSectorParameterAddGroup n07aNonlinearSectorParameterSMul
  n07aNonlinearSectorParameterSub

namespace N04RealizationGauge

/-- Uniform positive geometry data charge the reciprocal canonical width
of each right collar, even after the state neighborhood is shrunk.
The normalization buffer is explicit, so the estimate concerns the very
same supplied middle interval as the transport matching. -/
theorem n04PositiveGeometry_geometryData_forces_right_cost
    (G : N04RealizationGauge) (η : (G.W.S.height (3 / 4 : ℝ)).Space)
    {b : ℕ} {ε : ℝ} (hb : G.W.base ≤ b) (hε : 0 < ε) (hεW : ε ≤ G.W.ε)
    (hreference : N04PositiveReferenceFamily (G.W.A G.X.e₀) G.X.src 4 G.Y G.H)
    (href : ∀ i, G.τ (G.W.C.referenceState, 0) i = id)
    (buffer : N04PositiveNormalizationBuffer
      G.W.D.a G.W.D.b (deriv G.W.D.w) (tsupport G.W.D.chi))
    (lower upper : N04PositiveComponent G.W.D.a G.W.D.b (deriv G.W.D.w) → ℝ)
    (hmatching : ∀ z ∈ stateNeighborhood G.W.S G.W.C b ε,
      stateSector G.W.S z.1 → ∀ i,
      WholePositiveTransportMatching 3
        (fun side => n04PositiveSourceMap (G.X.src i side) (G.W.A G.X.e₀) z)
        (fun side => n04PositiveSourceHeight (G.X.src i side) (G.W.A G.X.e₀) z)
        (G.τ z i) (G.σ z i) (G.Q z i) (n04PositiveLeft i) (n04PositiveRight i)
        (buffer.centerLeft i) (buffer.centerRight i) (lower i) (upper i))
    (hdata : G.GeometryData η (G.Pos η) b ε) :
    ∃ loss : ℕ, ∃ B : ℝ, 0 < B ∧
      ∀ (i : N04PositiveComponent G.W.D.a G.W.D.b (deriv G.W.D.w))
        (k : ℕ), (G.X.src i true).val = some k →
        1 ≤ B * G.W.U.E0 (G.W.U.sample (G.X.cell i)) ^ B *
          G.W.U.H (G.W.U.sample (G.X.cell i)) ^ (3 / 4 : ℝ) *
          parameterGrading G.W.S (1 + loss)
            (n04PositiveGeometry_circleDirection G.W.hS k, 0) *
          (1 - G.Y i (buffer.centerRight i)) := by
  obtain ⟨loss, hvalue⟩ := (hdata.1 .inverseAngleDefect trivial).2.choose_spec.1
  obtain ⟨B, hB, hbound⟩ := hvalue 1
  refine ⟨loss, B, hB, ?_⟩
  intro i k hsource
  let m : ℕ := G.e.symm (.inr i)
  have hi : G.e m = .inr i := G.e.apply_symm_apply _
  obtain ⟨a, ha, _, hz⟩ := n04PositiveGeometry_circleDirection_small G.W.hS k b hε
  let z : Parameter G.W.S := (a • n04PositiveGeometry_circleDirection G.W.hS k, 0)
  have hzstate : G.lift η z ∈ stateNeighborhood G.W.S G.W.C b ε :=
    liftSectorParameter_mem_stateNeighborhood hz le_rfl
  have hzoriginal : G.lift η z ∈ stateNeighborhood G.W.S G.W.C G.W.base G.W.ε :=
    stateNeighborhood_mono G.W.S G.W.C hb hεW hzstate
  have hs : stateSector G.W.S (G.lift η z).1 :=
    G.W.through03.1.1.2.2.1.liftSectorParameter_sector z
  have hmatch := hmatching (G.lift η z) hzstate hs i
  have hfields := n04WholeReferenceGaugeAtlasData_positive_fields
    G.W.C G.W.L (G.W.A G.X.e₀) G.e G.X.cell
    (fun j => positiveReferenceCylinderChart (G.Y j))
    (fun j => positiveReferenceCylinderInverse (G.Y j))
    (fun j p => G.H j p.1) G.τ G.σ G.Q G.N (G.lift η z) m i hi
  have hcell : (G.V η).cell m = G.X.cell i := hfields.2.2.2.2.2.1
  have hpos : G.Pos η m := hfields.2.2.2.2.2.2.1
  have ho := buffer.ordered i
  have hcd : buffer.centerLeft i ≤ buffer.centerRight i :=
    ((ho.2.1.trans ho.2.2.1).trans ho.2.2.2.1).le
  have hld : n04PositiveLeft i < buffer.centerRight i :=
    ((ho.1.trans ho.2.1).trans ho.2.2.1).trans ho.2.2.2.1
  have hy : G.Y i (buffer.centerRight i) ∈ Ioo (0 : ℝ) 1 :=
    ((hreference i).1.maps_open
      (show (buffer.centerRight i, (0 : ℝ)) ∈
        Ioo (n04PositiveLeft i) (n04PositiveRight i) ×ˢ (univ : Set ℝ) from
        ⟨⟨hld, ho.2.2.2.2⟩, mem_univ _⟩)).1
  let θ : ℝ := Real.pi / 4 + a
  let f : ℝ → ℝ := fun y => G.atomFamily η .inverseAngleDefect z m (y, θ)
  have hfsmooth : ContDiff ℝ ∞ f :=
    (G.n04PositiveGeometry_inverseAngle_contDiff η m i hi hreference hmatch).comp
      (contDiff_id.prodMk contDiff_const)
  have hfmid : f (G.Y i (buffer.centerRight i)) = 0 :=
    G.n04PositiveGeometry_inverseAngle_middle_zero η m i hi hreference hmatch
      (buffer.centerRight i) ⟨hcd, le_rfl⟩ θ
  have hfend : |f 1| = a := by
    change |atom G.W.D G.W.U (G.S η) (G.C η) (G.L η) (G.V η)
      (G.lift η z) m .inverseAngleDefect (1, θ)| = a
    rw [G.n04PositiveGeometry_inverseAngle_endpoint η m i hi hreference
      hzoriginal hs hmatch true k hsource θ]
    exact n04PositiveGeometry_circleDirection_inverseRootLabel_displacement
      G.W.hS G.W.through03.1.1 k ha.le hzoriginal
  have hrefzero : ∀ p, G.atomRef η .inverseAngleDefect m p = 0 :=
    G.n04PositiveGeometry_inverseAngle_reference_zero η m i hi (href i)
  have hderiv : ∀ y ∈ Ioo (G.Y i (buffer.centerRight i)) 1,
      |deriv f y| ≤
        B * G.W.U.E0 (G.W.U.sample (G.X.cell i)) ^ B *
          G.W.U.H (G.W.U.sample (G.X.cell i)) ^ (3 / 4 : ℝ) *
          parameterGrading (G.S η) (1 + loss) z := by
    intro y hy'
    let q : unitStrip := ⟨(y, θ), ⟨⟨hy.1.trans hy'.1, hy'.2⟩, mem_univ _⟩⟩
    have h := hbound z hz m hpos q 1 0 (by norm_num)
    simpa only [mixedDerivative, iteratedDeriv_one, iteratedDeriv_zero,
      hrefzero, sub_zero, hcell, f] using h
  have hjump := n04PositiveGeometry_endpointJump_le hy.2
    hfsmooth.continuous.continuousOn
    (hfsmooth.differentiable (by simp)).differentiableOn hderiv
  rw [hfmid, sub_zero, hfend] at hjump
  have hscale : parameterGrading (G.S η) (1 + loss) z =
      a * parameterGrading G.W.S (1 + loss)
        (n04PositiveGeometry_circleDirection G.W.hS k, 0) :=
    n04PositiveGeometry_circleDirection_parameterGrading G.W.hS k (1 + loss) ha.le
  rw [hscale] at hjump
  apply n04PositiveGeometry_cancel_amplitude ha
  calc
    a ≤ (B * G.W.U.E0 (G.W.U.sample (G.X.cell i)) ^ B *
        G.W.U.H (G.W.U.sample (G.X.cell i)) ^ (3 / 4 : ℝ) *
        (a * parameterGrading G.W.S (1 + loss)
          (n04PositiveGeometry_circleDirection G.W.hS k, 0))) *
        (1 - G.Y i (buffer.centerRight i)) := hjump
    _ = (B * G.W.U.E0 (G.W.U.sample (G.X.cell i)) ^ B *
        G.W.U.H (G.W.U.sample (G.X.cell i)) ^ (3 / 4 : ℝ) *
        parameterGrading G.W.S (1 + loss)
          (n04PositiveGeometry_circleDirection G.W.hS k, 0) * a) *
        (1 - G.Y i (buffer.centerRight i)) := by ring

end N04RealizationGauge

end ContinuousFlexibility.Analysis
