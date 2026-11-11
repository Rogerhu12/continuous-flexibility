import ContinuousFlexibility.Radial.InnerRadialModelPoissonPiece
import ContinuousFlexibility.Radial.InnerRadialGapPiece
import ContinuousFlexibility.Radial.InnerModelPoissonAssembly
import ContinuousFlexibility.Radial.InnerModelDirichletCost

/-!
# Actual model and gap data on one common finite chain

The input records contain the original localized model witness and its
physical chart, or the actual positive-gap coefficients and classical
columns. Local weak existence, uniqueness, and conormal identities are
derived from these data. None is an input field.

The finite-chain assembly below uses these exact Hilbert Dirichlet and
Poisson operators. The model inverse is the existing Hilbert transport;
the positive-gap operator sends its field into the scalar-zero summand.
-/

noncomputable section

namespace ContinuousFlexibility.Radial

open Set MeasureTheory ContinuousFlexibility.Statements
open scoped ContDiff InnerProductSpace BigOperators

/-- Physical chart data for the same already constructed localized R09
model. Any identification with a particular Morse or central buffer is
made by the outer coefficient construction. -/
structure InnerRadialModelChart (D : ReferenceData) {n : ℕ}
    (G : InnerRadialChainGeometry D n) (bordered : Bool) (j : ℝ)
    (central : Fin (n + 1)) (column : RadialModeL2 D) (piece : Fin (n + 1)) where
  buffer : BufferData
  buffer_hypotheses : BufferHypotheses buffer
  C : ℝ
  K : ℝ
  localized : InnerBufferLocalizedData buffer C K
  radius : ℝ → ℝ
  scale : ℝ → ℝ
  height : ℝ
  height_pos : 0 < height
  radius_smooth : ContDiff ℝ ∞ radius
  scale_smooth : ContDiff ℝ ∞ scale
  chart_pos : ∀ x ∈ Icc buffer.l buffer.h,
    0 < radius x ∧ 0 < deriv radius x ∧ 0 < scale x
  in_core : Ioo (radius buffer.l) (radius buffer.h) ⊆ radialCore D
  weight_identity : ∀ x ∈ Icc buffer.l buffer.h,
    D.w (radius x) = height * scale x ^ 2 * deriv radius x
  U : ℝ
  U_nonneg : 0 ≤ U
  log_deriv_bound : ∀ x ∈ Icc buffer.l buffer.h, |deriv radius x / radius x| ≤ U
  potential_identity : ∀ x ∈ Ioo buffer.l buffer.h,
    buffer.potential x = liouvilleV0 scale x - j ^ 2 * liouvilleRho radius scale x
  left_eq : G.left piece = radius buffer.l
  right_eq : G.right piece = radius buffer.h
  bordered_eq : buffer.bordered = if piece = central then bordered else false
  column_eq : piece = central →
    innerLiouvilleColumnLift D buffer_hypotheses.1.le height_pos radius_smooth
      scale_smooth chart_pos in_core weight_identity buffer.border = column

/-- The positive-gap data are the true coefficients and the same
classical columns constructed by the radial IVP theorem. No gap inverse
or flux identity is stored here. -/
structure InnerRadialGapChart (D : ReferenceData) {n : ℕ}
    (G : InnerRadialChainGeometry D n) (j : ℝ)
    (central piece : Fin (n + 1)) where
  away_center : piece ≠ central
  frequency_pos : 0 < j
  slope : ℝ
  slope_pos : 0 < slope
  slope_lower : ∀ r ∈ Icc (G.left piece) (G.right piece),
    slope ≤ r * deriv D.w r / D.w r
  columns : Fin 2 → ℝ → ℝ
  columns_smooth : ∀ i, ContDiff ℝ ∞ (columns i)
  columns_boundary : ∀ i k,
    columns k (innerGapEndpoint (G.left piece) (G.right piece) i) = if k = i then 1 else 0
  columns_homogeneous : ∀ i r, r ∈ Icc (G.left piece) (G.right piece) →
    radialJacobi (j ^ 2) D.w (columns i) r = 0

abbrev InnerRadialActualPiece (D : ReferenceData) {n : ℕ}
    (G : InnerRadialChainGeometry D n) (bordered : Bool) (j : ℝ)
    (central : Fin (n + 1)) (column : RadialModeL2 D) (piece : Fin (n + 1)) :=
  Sum (InnerRadialModelChart D G bordered j central column piece)
    (InnerRadialGapChart D G j central piece)

/-- Inclusion of a physical field with zero scalar. -/
def innerRadialFieldZeroLift (D : ReferenceData) :
    RadialModeL2 D →L[ℝ] InnerBorderL2 (radialHilbertMeasure D) :=
  ((innerBorderMaxEquiv (radialHilbertMeasure D)).symm :
    (RadialModeL2 D × ℝ) →L[ℝ] InnerBorderL2 (radialHilbertMeasure D)) ∘L
      ContinuousLinearMap.inl ℝ (RadialModeL2 D) ℝ

@[simp] theorem innerRadialFieldZeroLift_apply (D : ReferenceData) (u : RadialModeL2 D) :
    innerRadialFieldZeroLift D u = WithLp.toLp 2 (u, (0 : ℝ)) := by
  simp only [innerRadialFieldZeroLift, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearEquiv.coe_coe,
    innerBorderMaxEquiv_symm_apply]

namespace InnerRadialModelChart

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  {piece : Fin (n + 1)} (A : InnerRadialModelChart D G bordered j central column piece)

def dirichlet : InnerBorderL2 (radialHilbertMeasure D) →L[ℝ]
    InnerBorderL2 (radialHilbertMeasure D) :=
  innerLiouvilleHilbertDirichlet D A.buffer_hypotheses.1.le A.height_pos A.radius_smooth
    A.scale_smooth A.chart_pos A.in_core A.weight_identity A.U A.U_nonneg
    A.log_deriv_bound A.localized.dirichlet

def column (i : Fin 2) : InnerBorderL2 (radialHilbertMeasure D) :=
  innerModelPhysicalPoissonColumn D A.buffer_hypotheses A.localized A.height_pos
    A.radius_smooth A.scale_smooth A.chart_pos A.in_core A.weight_identity
    A.U A.U_nonneg A.log_deriv_bound i

def poisson : EuclideanSpace ℝ (Fin 2) →L[ℝ] InnerBorderL2 (radialHilbertMeasure D) :=
  innerTwoColumnMap A.column

def kappa (i : Fin 2) : ℝ :=
  innerLiouvilleBoundaryKappa A.height A.scale (bufferCut A.buffer)
    (fun i => (A.localized.column i).inwardEnergy) i

def errorMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  A.localized.physicalFluxError A.height (fun i => A.scale (bufferCut A.buffer i))

theorem poisson_apply (z : EuclideanSpace ℝ (Fin 2)) :
    A.poisson z = WithLp.toLp 2
      (z 0 • innerLiouvilleUnitPoissonPair D A.buffer_hypotheses.1.le A.height_pos
        A.radius_smooth A.scale_smooth A.chart_pos A.in_core A.weight_identity
        A.U A.U_nonneg A.log_deriv_bound (bufferCut A.buffer 0)
        (A.localized.column 0).field (A.localized.column 0).scalar +
       z 1 • innerLiouvilleUnitPoissonPair D A.buffer_hypotheses.1.le A.height_pos
        A.radius_smooth A.scale_smooth A.chart_pos A.in_core A.weight_identity
        A.U A.U_nonneg A.log_deriv_bound (bufferCut A.buffer 1)
        (A.localized.column 1).field (A.localized.column 1).scalar) := by
  simp only [poisson, innerTwoColumnMap_apply, Fin.sum_univ_two, InnerRadialModelChart.column,
    innerModelPhysicalPoissonColumn, WithLp.toLp_add, WithLp.toLp_smul]

theorem kernelUnique (hw : ContDiff ℝ ∞ D.w) :
    InnerRadialPieceKernelUnique D G bordered j central column piece :=
  innerRadialModelPieceKernelUnique D G bordered j central column piece
    A.buffer_hypotheses A.localized A.height_pos A.radius_smooth A.scale_smooth
    A.chart_pos A.in_core A.weight_identity A.U A.U_nonneg A.log_deriv_bound hw
    A.potential_identity A.left_eq A.right_eq A.bordered_eq A.column_eq

end InnerRadialModelChart

namespace InnerRadialGapChart

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {j : ℝ} {central piece : Fin (n + 1)} (A : InnerRadialGapChart D G j central piece)

def fieldDirichlet (hw : ContDiff ℝ ∞ D.w) : RadialModeL2 D →L[ℝ] RadialModeL2 D :=
  innerGapDirichletInverse D hw (G.left_lt_right piece).le (G.left_pos piece)
    A.frequency_pos A.slope_pos (G.in_core piece) (G.weight_pos piece) A.slope_lower

def dirichlet (hw : ContDiff ℝ ∞ D.w) :
    InnerBorderL2 (radialHilbertMeasure D) →L[ℝ] InnerBorderL2 (radialHilbertMeasure D) :=
  innerRadialFieldZeroLift D ∘L A.fieldDirichlet hw ∘L
    WithLp.fstL 2 ℝ (RadialModeL2 D) ℝ

def fieldPoisson (hw : Continuous D.w) : EuclideanSpace ℝ (Fin 2) →L[ℝ] RadialModeL2 D :=
  innerGapPoissonL2 D hw (G.left_pos piece) (G.in_core piece)
    (fun r hr => (G.weight_pos piece r (Ioo_subset_Icc_self hr)).le)
    A.columns A.columns_smooth

def poisson (hw : Continuous D.w) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] InnerBorderL2 (radialHilbertMeasure D) :=
  innerRadialFieldZeroLift D ∘L A.fieldPoisson hw

def fluxMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  innerGapFluxMatrix D.w (G.left piece) (G.right piece) A.columns

@[simp] theorem dirichlet_apply (hw : ContDiff ℝ ∞ D.w)
    (F : InnerBorderL2 (radialHilbertMeasure D)) :
    A.dirichlet hw F = WithLp.toLp 2 (A.fieldDirichlet hw F.fst, (0 : ℝ)) := by
  simp only [dirichlet, ContinuousLinearMap.comp_apply, WithLp.fstL_apply,
    innerRadialFieldZeroLift_apply]

@[simp] theorem poisson_apply (hw : Continuous D.w) (z : EuclideanSpace ℝ (Fin 2)) :
    A.poisson hw z = WithLp.toLp 2 (A.fieldPoisson hw z, (0 : ℝ)) := by
  simp only [poisson, ContinuousLinearMap.comp_apply, innerRadialFieldZeroLift_apply]

theorem kernelUnique (hw : ContDiff ℝ ∞ D.w) (bordered : Bool) (column : RadialModeL2 D) :
    InnerRadialPieceKernelUnique D G bordered j central column piece :=
  innerRadialGapPieceKernelUnique D hw G bordered j central column piece A.away_center
    A.frequency_pos A.slope A.slope_pos A.slope_lower

end InnerRadialGapChart

namespace InnerRadialActualPiece

variable {D : ReferenceData} {n : ℕ} {G : InnerRadialChainGeometry D n}
  {bordered : Bool} {j : ℝ} {central : Fin (n + 1)} {column : RadialModeL2 D}
  {piece : Fin (n + 1)} (A : InnerRadialActualPiece D G bordered j central column piece)

def dirichlet (hw : ContDiff ℝ ∞ D.w) :
    InnerBorderL2 (radialHilbertMeasure D) →L[ℝ] InnerBorderL2 (radialHilbertMeasure D) :=
  match A with
  | .inl M => M.dirichlet
  | .inr Q => Q.dirichlet hw

def poisson (hw : Continuous D.w) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] InnerBorderL2 (radialHilbertMeasure D) :=
  match A with
  | .inl M => M.poisson
  | .inr Q => Q.poisson hw

def kappa : Fin 2 → ℝ :=
  match A with
  | .inl M => M.kappa
  | .inr _ => 0

def gapMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  match A with
  | .inl _ => 0
  | .inr Q => Q.fluxMatrix

def errorMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  match A with
  | .inl M => M.errorMatrix
  | .inr _ => 0

def referenceMatrix : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal A.kappa + A.gapMatrix

theorem kernelUnique (hw : ContDiff ℝ ∞ D.w) :
    InnerRadialPieceKernelUnique D G bordered j central column piece := by
  cases A with
  | inl M => exact M.kernelUnique hw
  | inr Q => exact Q.kernelUnique hw bordered column

end InnerRadialActualPiece

end ContinuousFlexibility.Radial
