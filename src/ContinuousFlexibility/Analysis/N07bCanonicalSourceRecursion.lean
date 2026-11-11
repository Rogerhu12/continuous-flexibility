import ContinuousFlexibility.Analysis.N07bCanonicalInverseAngle
import ContinuousFlexibility.Analysis.N07bCanonicalSourceJets
import ContinuousFlexibility.Analysis.BoundaryMixedJets

/-!
# Physical recursion for the actual canonical angular source jets

The zeroth physical expression is the prescribed source factor `h f / |J|`.
Every subsequent expression applies the actual inverse angular vector field
to the preceding expression. The chart's genuine inverse identity proves
that these expressions are exactly the angular jets of `canonicalSource`.

Smoothness of all recursive expressions follows from Part A and physical
smoothness on the closed piece. No derivative formula or uniform geometric
bound is added as a hypothesis.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The actual inverse angular vector acting on a physical scalar. -/
def n07bInverseAngleDerivative (Ψ : PolarPoint → PolarPoint)
    (F : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  (n07bInverseAngleVector Ψ x).1 * radialPartial F x +
    (n07bInverseAngleVector Ψ x).2 * angularPartial F x

/-- Smoothness of the actual inverse angular vector is a consequence of
smoothness and the nonzero actual Jacobian of the forward chart. -/
theorem n07b_contDiffAt_inverseAngleVector
    {Ψ : PolarPoint → PolarPoint} {x : PolarPoint}
    (hΨ : ContDiffAt ℝ ∞ Ψ x) (hJ : planeJacobian Ψ x ≠ 0) :
    ContDiffAt ℝ ∞ (n07bInverseAngleVector Ψ) x := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ Ψ) x := hΨ.fderiv_right (by simp)
  have hr := hd.clm_apply (contDiffAt_const (c := ((1, 0) : PolarPoint)))
  have hθ := hd.clm_apply (contDiffAt_const (c := ((0, 1) : PolarPoint)))
  have hj := ContinuousFlexibility.contDiffAt_planeJacobian hΨ
  change ContDiffAt ℝ ∞
    (fun y => (-(fderiv ℝ Ψ y (0, 1)).1 / planeJacobian Ψ y,
      (fderiv ℝ Ψ y (1, 0)).1 / planeJacobian Ψ y)) x
  exact (hθ.fst.neg.div hj hJ).prodMk (hr.fst.div hj hJ)

/-- Applying the inverse angular direction preserves local smoothness. -/
theorem n07b_contDiffAt_inverseAngleDerivative
    {Ψ : PolarPoint → PolarPoint} {F : PolarPoint → ℝ} {x : PolarPoint}
    (hΨ : ContDiffAt ℝ ∞ Ψ x) (hJ : planeJacobian Ψ x ≠ 0)
    (hF : ContDiffAt ℝ ∞ F x) :
    ContDiffAt ℝ ∞ (n07bInverseAngleDerivative Ψ F) x := by
  have hV := n07b_contDiffAt_inverseAngleVector hΨ hJ
  change ContDiffAt ℝ ∞
    (fun y => (n07bInverseAngleVector Ψ y).1 * radialPartial F y +
      (n07bInverseAngleVector Ψ y).2 * angularPartial F y) x
  exact (hV.fst.mul (contDiffAt_radialPartial hF (by simp))).add
    (hV.snd.mul (contDiffAt_angularPartial hF (by simp)))

/-- Physical expressions whose pullbacks are the actual angular source
jets. This definition involves only the forward chart and its derivatives. -/
def n07bPhysicalSourceJet {S : PhysicalSpacesData} (K : CanonicalData S)
    (z : AnnularState S × ℝ) (m : ℕ) (f : PolarPoint → ℝ) :
    ℕ → PolarPoint → ℝ
  | 0 => fun x => K.height z m x * f x / |planeJacobian (K.chart z m) x|
  | j + 1 => n07bInverseAngleDerivative (K.chart z m)
      (n07bPhysicalSourceJet K z m f j)

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  (hK : N04PartA D S C K base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1)

include hK hz hs

/-- Every recursive expression is smooth at every physical closed-piece
point where the original source is smooth. -/
theorem n07b_contDiffAt_physicalSourceJet (m : ℕ)
    {f : PolarPoint → ℝ} {x : PolarPoint}
    (hx : x ∈ physicalPieceClosed S K z m)
    (hf : ContDiffAt ℝ ∞ f x) (j : ℕ) :
    ContDiffAt ℝ ∞ (n07bPhysicalSourceJet K z m f j) x := by
  have hclosed := (hK.boundary z hz hs m).2.2.2.2.1 x hx
  induction j with
  | zero =>
      exact n07b_contDiffAt_physicalSourceFactor hK hz hs m hx hf
  | succ j ih =>
      exact n07b_contDiffAt_inverseAngleDerivative hclosed.1 hclosed.2.2.1 ih

/-- The physical recursion equals the actual canonical angular derivative
at the actual chart image. The induction differentiates equality on the
canonical open piece, so it never uses endpoint values of the inverse. -/
theorem n07b_canonicalSource_angularJet_comp_chart (m : ℕ)
    {f : PolarPoint → ℝ}
    (hf : ∀ x ∈ physicalPieceClosed S K z m, ContDiffAt ℝ ∞ f x)
    (j : ℕ) {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K z m) :
    mixedDerivative 0 j (canonicalSource S K z m f) (K.chart z m x) =
      n07bPhysicalSourceJet K z m f j x := by
  have hcharts := hK.charts z hz hs m
  have hopen : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have hsource := n07b_contDiffOn_canonicalSource hK hz hs m hf
  induction j generalizing x with
  | zero =>
      simp only [mixedDerivative, iteratedDeriv_zero, Prod.eta]
      change K.height z m (K.inverseChart z m (K.chart z m x)) *
          f (K.inverseChart z m (K.chart z m x)) /
          |planeJacobian (K.chart z m) (K.inverseChart z m (K.chart z m x))| =
        K.height z m x * f x / |planeJacobian (K.chart z m) x|
      rw [hcharts.2.2.1 x hx]
  | succ j ih =>
      have heq : EqOn (mixedDerivative 0 j (canonicalSource S K z m f))
          (n07bPhysicalSourceJet K z m f j ∘ K.inverseChart z m)
          (canonicalOpen S K m) := by
        intro p hp
        have h := ih (x := K.inverseChart z m p) (hcharts.2.1 hp)
        rw [hcharts.2.2.2.1 p hp] at h
        exact h
      have hgerm : mixedDerivative 0 j (canonicalSource S K z m f) =ᶠ[𝓝 (K.chart z m x)]
          (n07bPhysicalSourceJet K z m f j ∘ K.inverseChart z m) := by
        filter_upwards [hopen.mem_nhds (hcharts.1 hx)] with p hp
        exact heq hp
      have hxclosed : x ∈ physicalPieceClosed S K z m := subset_closure hx
      have hd : DifferentiableAt ℝ (n07bPhysicalSourceJet K z m f j) x :=
        (n07b_contDiffAt_physicalSourceJet hK hz hs m hxclosed (hf x hxclosed) j).differentiableAt
          (by simp)
      calc
        mixedDerivative 0 (j + 1) (canonicalSource S K z m f) (K.chart z m x) =
            angularPartial (mixedDerivative 0 j (canonicalSource S K z m f))
              (K.chart z m x) :=
          (angularPartial_mixedDerivative_on_open hopen hsource 0 j (hcharts.1 hx)).symm
        _ = angularPartial (n07bPhysicalSourceJet K z m f j ∘ K.inverseChart z m)
              (K.chart z m x) :=
          congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (0, 1))
            (hgerm.fderiv_eq (𝕜 := ℝ))
        _ = n07bInverseAngleDerivative (K.chart z m)
              (n07bPhysicalSourceJet K z m f j) x :=
          n07b_canonical_angularPartial_comp_inverse hK hz hs m hx hd
        _ = n07bPhysicalSourceJet K z m f (j + 1) x := rfl

/-- The same exact identity stated at a canonical point. -/
theorem n07b_canonicalSource_angularJet_eq_physical (m : ℕ)
    {f : PolarPoint → ℝ}
    (hf : ∀ x ∈ physicalPieceClosed S K z m, ContDiffAt ℝ ∞ f x)
    (j : ℕ) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    mixedDerivative 0 j (canonicalSource S K z m f) p =
      n07bPhysicalSourceJet K z m f j (K.inverseChart z m p) := by
  have hcharts := hK.charts z hz hs m
  have h := n07b_canonicalSource_angularJet_comp_chart hK hz hs m hf j (hcharts.2.1 hp)
  rwa [hcharts.2.2.2.1 p hp] at h

/-- Globally smooth physical sources need no additional local smoothness
input for the actual derivative identity. -/
theorem n07b_canonicalSource_angularJet_comp_chart_of_contDiff (m : ℕ)
    {f : PolarPoint → ℝ} (hf : ContDiff ℝ ∞ f) (j : ℕ)
    {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K z m) :
    mixedDerivative 0 j (canonicalSource S K z m f) (K.chart z m x) =
      n07bPhysicalSourceJet K z m f j x :=
  n07b_canonicalSource_angularJet_comp_chart hK hz hs m
    (fun _ _ => hf.contDiffAt) j hx

end ContinuousFlexibility.Analysis
