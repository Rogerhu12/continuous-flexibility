import ContinuousFlexibility.Analysis.N06CurrentTestLp

/-!
# Actual inverse-coordinate test jets on the closed canonical strip

The adjugate of the genuine forward derivative gives two physical vector
fields for differentiating a pullback through the current inverse chart.
They are smooth at every physical boundary point because N04 gives the
actual forward chart smoothness and a nonzero Jacobian there. Iterating
these physical vector fields expresses the first two canonical test jets
as pullbacks of continuous functions on the compact physical tile.
Consequently they lie in the original canonical L2 space. The genuine boundary inverse germs also give smoothness on the full closed
canonical strip, which supplies the finite-measure bounds for the actual tests.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- The actual inverse derivative applied to a fixed coordinate vector,
written on the physical side using the forward derivative's adjugate. -/
def n06InverseChartVector (F : PolarPoint → PolarPoint) (v : PolarPoint)
    (x : PolarPoint) : PolarPoint :=
  (((fderiv ℝ F x (0, 1)).2 * v.1 - (fderiv ℝ F x (0, 1)).1 * v.2) /
      planeJacobian F x,
    ((fderiv ℝ F x (1, 0)).1 * v.2 - (fderiv ℝ F x (1, 0)).2 * v.1) /
      planeJacobian F x)

/-- Differentiation in a fixed canonical direction, kept as an actual
function of the physical point. -/
def n06InverseChartDerivative (F : PolarPoint → PolarPoint) (v : PolarPoint)
    (f : PolarPoint → ℝ) (x : PolarPoint) : ℝ :=
  fderiv ℝ f x (n06InverseChartVector F v x)

private theorem plane_clm_apply (A : PolarPoint →L[ℝ] PolarPoint) (v : PolarPoint) :
    A v = v.1 • A (1, 0) + v.2 • A (0, 1) := by
  have hv : v = v.1 • (1, 0) + v.2 • (0, 1) := by
    ext <;> simp
  calc
    A v = A (v.1 • (1, 0) + v.2 • (0, 1)) := congrArg A hv
    _ = _ := by rw [map_add, map_smul, map_smul]

/-- The adjugate field is a true right inverse of the forward derivative. -/
theorem n06_fderiv_inverseChartVector
    (F : PolarPoint → PolarPoint) (v : PolarPoint) {x : PolarPoint}
    (hJ : planeJacobian F x ≠ 0) :
    fderiv ℝ F x (n06InverseChartVector F v x) = v := by
  rw [plane_clm_apply]
  have hJ' : (fderiv ℝ F x (1, 0)).1 * (fderiv ℝ F x (0, 1)).2 -
      (fderiv ℝ F x (1, 0)).2 * (fderiv ℝ F x (0, 1)).1 ≠ 0 := hJ
  have hJ'' : (fderiv ℝ F x (0, 1)).2 * (fderiv ℝ F x (1, 0)).1 -
      (fderiv ℝ F x (0, 1)).1 * (fderiv ℝ F x (1, 0)).2 ≠ 0 := by
    simpa only [mul_comm] using hJ'
  apply Prod.ext <;>
    simp only [n06InverseChartVector, planeJacobian, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul] <;>
    field_simp [hJ', hJ''] <;> ring

/-- Only the genuine forward chart is differentiated at the boundary. -/
theorem n06InverseChartVector_contDiffAt
    {F : PolarPoint → PolarPoint} (v : PolarPoint) {x : PolarPoint}
    (hF : ContDiffAt ℝ ∞ F x) (hJ : planeJacobian F x ≠ 0) :
    ContDiffAt ℝ ∞ (n06InverseChartVector F v) x := by
  have hd : ContDiffAt ℝ ∞ (fderiv ℝ F) x := hF.fderiv_right (by simp)
  have hr : ContDiffAt ℝ ∞ (fun q => fderiv ℝ F q (1, 0)) x :=
    hd.clm_apply contDiffAt_const
  have ht : ContDiffAt ℝ ∞ (fun q => fderiv ℝ F q (0, 1)) x :=
    hd.clm_apply contDiffAt_const
  have hdet : ContDiffAt ℝ ∞ (planeJacobian F) x :=
    (hr.fst.mul ht.snd).sub (hr.snd.mul ht.fst)
  exact (((ht.snd.mul contDiffAt_const).sub (ht.fst.mul contDiffAt_const)).div hdet hJ).prodMk
    (((hr.fst.mul contDiffAt_const).sub (hr.snd.mul contDiffAt_const)).div hdet hJ)

theorem n06InverseChartDerivative_contDiffAt
    {F : PolarPoint → PolarPoint} (v : PolarPoint) {f : PolarPoint → ℝ}
    {x : PolarPoint} (hF : ContDiffAt ℝ ∞ F x) (hJ : planeJacobian F x ≠ 0)
    (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (n06InverseChartDerivative F v f) x :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply
    (n06InverseChartVector_contDiffAt v hF hJ)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology ENNReal

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ} {z : AnnularState S × ℝ}

/-- Differentiating the original inverse identity identifies its actual
derivative with the physical adjugate vector field. -/
theorem n06_current_inverseChart_fderiv_apply
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (v : PolarPoint) {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    fderiv ℝ (K.inverseChart z m) p v =
      n06InverseChartVector (K.chart z m) v (K.inverseChart z m p) := by
  let x := K.inverseChart z m p
  have hc := h04.1.charts z hz hs m
  have hx : x ∈ physicalPieceOpen S K z m := hc.2.1 hp
  have hFx : K.chart z m x = p := hc.2.2.2.1 p hp
  have hF : DifferentiableAt ℝ (K.chart z m) x :=
    (hc.2.2.2.2.1.contDiffAt ((h04.1.domains z hz hs m).1.mem_nhds hx)).differentiableAt
      (by simp)
  have hG : DifferentiableAt ℝ (K.inverseChart z m) (K.chart z m x) := by
    rw [hFx]
    exact (hc.2.2.2.2.2.1.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  have he : K.inverseChart z m ∘ K.chart z m =ᶠ[𝓝 x] id := by
    filter_upwards [(h04.1.domains z hz hs m).1.mem_nhds hx] with q hq
    exact hc.2.2.1 q hq
  have hd := he.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp x hG hF, fderiv_id, hFx] at hd
  have hv := n06_fderiv_inverseChartVector (K.chart z m) v
    (hc.2.2.2.2.2.2.2 x hx).2.1
  have hh := congrArg (fun A : PolarPoint →L[ℝ] PolarPoint =>
    A (n06InverseChartVector (K.chart z m) v x)) hd
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hv] using hh

/-- The chain rule is expressed entirely by an actual physical field. -/
theorem n06_current_inverseChart_comp_fderiv
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (v : PolarPoint) {f : PolarPoint → ℝ}
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m)
    (hf : DifferentiableAt ℝ f (K.inverseChart z m p)) :
    fderiv ℝ (fun q => f (K.inverseChart z m q)) p v =
      n06InverseChartDerivative (K.chart z m) v f (K.inverseChart z m p) := by
  have hc := h04.1.charts z hz hs m
  have hG : DifferentiableAt ℝ (K.inverseChart z m) p :=
    (hc.2.2.2.2.2.1.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hp)).differentiableAt (by simp)
  rw [fderiv_fun_comp p hf hG, ContinuousLinearMap.comp_apply,
    n06_current_inverseChart_fderiv_apply h04 hz hs m v hp]
  rfl

/-- A second actual canonical derivative is another physical vector-field
derivative. Equality of the first jets is used on a neighborhood, so this
does not treat pointwise equality as derivative equality. -/
theorem n06_current_inverseChart_comp_second
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (v w : PolarPoint) {f : PolarPoint → ℝ}
    (hf : ∀ x : PolarPoint, x ∈ physicalPieceClosed S K z m →
      ContDiffAt ℝ ∞ f x)
    {p : PolarPoint} (hp : p ∈ canonicalOpen S K m) :
    fderiv ℝ (fun q => fderiv ℝ (fun t => f (K.inverseChart z m t)) q v) p w =
      n06InverseChartDerivative (K.chart z m) w
        (n06InverseChartDerivative (K.chart z m) v f) (K.inverseChart z m p) := by
  have hc := h04.1.charts z hz hs m
  have hb := (h04.1.boundary z hz hs m).2.2.2.2.1
  have hfirst : (fun q => fderiv ℝ (fun t => f (K.inverseChart z m t)) q v)
      =ᶠ[𝓝 p] fun q =>
        n06InverseChartDerivative (K.chart z m) v f (K.inverseChart z m q) := by
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    exact n06_current_inverseChart_comp_fderiv h04 hz hs m v hq
      ((hf _ (subset_closure (hc.2.1 hq))).differentiableAt (by simp))
  have hx := subset_closure (hc.2.1 hp)
  have hjet := n06InverseChartDerivative_contDiffAt v
    (hb _ hx).1 (hb _ hx).2.2.1 (hf _ hx)
  calc
    _ = fderiv ℝ (fun q =>
        n06InverseChartDerivative (K.chart z m) v f (K.inverseChart z m q)) p w :=
      congrArg (fun A : PolarPoint →L[ℝ] ℝ => A w) (hfirst.fderiv_eq (𝕜 := ℝ))
    _ = _ := n06_current_inverseChart_comp_fderiv h04 hz hs m w hp
      (hjet.differentiableAt (by simp))

/-- The first and second derivatives of the actual current height test
belong to the original L2 space. All compact bounds come from N04's true
closed forward-chart jets, and hold for arbitrary fixed directions. -/
theorem n06_current_canonicalHeight_directionalJets_memLp
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) (v w : PolarPoint) {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    MemLp (fun p => fderiv ℝ (canonicalHeight S K z m φ) p v)
      2 (canonicalMeasure S K m) ∧
    MemLp (fun p => fderiv ℝ
      (fun q => fderiv ℝ (canonicalHeight S K z m φ) q v) p w)
      2 (canonicalMeasure S K m) := by
  have hH (p : PolarPoint) (hp : p ∈ canonicalClosed S K m) :
      ContDiffAt ℝ ∞ (canonicalHeight S K z m φ) p :=
    n04b_canonicalHeight_contDiffAt_closed h04.1 hz hs m hp hφ
  have hfirst (p : PolarPoint) (hp : p ∈ canonicalClosed S K m) :
      ContDiffAt ℝ ∞
        (fun q => fderiv ℝ (canonicalHeight S K z m φ) q v) p :=
    ((hH p hp).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const
  constructor
  · apply n06_memLp_canonical_of_continuousOn_closed m
    intro p hp
    exact (hfirst p ⟨hp.1, mem_univ _⟩).continuousAt.continuousWithinAt
  · apply n06_memLp_canonical_of_continuousOn_closed m
    intro p hp
    exact (((hfirst p ⟨hp.1, mem_univ _⟩).fderiv_right (m := ∞) (by simp)).clm_apply
      contDiffAt_const).continuousAt.continuousWithinAt

theorem n06_current_canonicalHeight_second_memLp
    (h04 : N04Properties D T S C L K base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (m : ℕ) {φ : PolarPoint → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    MemLp (radialPartial (radialPartial (canonicalHeight S K z m φ)))
      2 (canonicalMeasure S K m) ∧
    MemLp (angularPartial (angularPartial (canonicalHeight S K z m φ)))
      2 (canonicalMeasure S K m) :=
  ⟨(n06_current_canonicalHeight_directionalJets_memLp h04 hz hs m (1, 0) (1, 0) hφ).2,
    (n06_current_canonicalHeight_directionalJets_memLp h04 hz hs m (0, 1) (0, 1) hφ).2⟩

end ContinuousFlexibility.Statements
