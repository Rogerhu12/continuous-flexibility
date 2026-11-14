module

public import ContinuousFlexibility.Analysis.CoupledControlLift
public import ContinuousFlexibility.Analysis.CoupledCircleParity
public import ContinuousFlexibility.Analysis.StateKappaBounds

/-!
# Linear recovery of the full coupled increment

The Banach control solution is lifted by its own mean equation. The height,
scalar parameter, constant control and odd chart are then assembled as actual
linear maps of the independent source. A total representative is zero away
from the neighborhood where the Neumann criterion holds; its sector-valued
version is a codomain restriction of exactly the same map.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

def coupledSourceLinear (S : PhysicalSpacesData) : ResidualSpace S →ₗ[ℝ] S.Source :=
  LinearMap.fst ℝ S.Source (EvenCircle S)

def coupledCircleLinear (S : PhysicalSpacesData) : ResidualSpace S →ₗ[ℝ] CircleSpace S :=
  (evenCircleSubmodule S).subtype.comp (LinearMap.snd ℝ S.Source (EvenCircle S))

theorem coupledSourceLinear_apply (S : PhysicalSpacesData) (y : ResidualSpace S) :
    coupledSourceLinear S y = y.1 := rfl

theorem coupledCircleLinear_apply (S : PhysicalSpacesData) (y : ResidualSpace S) :
    coupledCircleLinear S y = y.2.val := rfl

/-- The original control solution, retaining its linear dependence on the
complete scalar/circle source. -/
def coupledControlSolutionLinear (B : ControlColumnData S) (G : ScalarInverseData S)
    (N : ControlInverseData S) (z : AnnularState S × ℝ) :
    ResidualSpace S →ₗ[ℝ] ControlBanach :=
  (N.inverse z).toLinearMap.comp ((B.JInverse z).toLinearMap.comp
    (B.restriction.toLinearMap.comp (coupledCircleLinear S) -
      z.2 • (controlMeanRow S B z).toLinearMap.comp
        ((LinearMap.fst ℝ (HeightPair S) ℝ).comp
          ((G.G z).toLinearMap.comp (coupledSourceLinear S)))))

theorem coupledControlSolutionLinear_apply
    (B : ControlColumnData S) (G : ScalarInverseData S) (N : ControlInverseData S)
    (z : AnnularState S × ℝ) (y : ResidualSpace S) :
    coupledControlSolutionLinear B G N z y = controlSolution S B G N z y := by
  simp only [coupledControlSolutionLinear, controlSolution, LinearMap.comp_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.fst_apply,
    coupledCircleLinear_apply, coupledSourceLinear_apply, ContinuousLinearMap.coe_coe]

def coupledRecoveredHeightLinear (B : ControlColumnData S) (G : ScalarInverseData S)
    (N : ControlInverseData S) (z : AnnularState S × ℝ) :
    ResidualSpace S →ₗ[ℝ] HeightPair S × ℝ :=
  (G.G z).toLinearMap.comp (coupledSourceLinear S) -
    ((G.G z).toLinearMap.comp (B.heightColumn z).toLinearMap).comp
      (coupledControlSolutionLinear B G N z)

theorem coupledRecoveredHeightLinear_apply
    (B : ControlColumnData S) (G : ScalarInverseData S) (N : ControlInverseData S)
    (z : AnnularState S × ℝ) (y : ResidualSpace S) :
    coupledRecoveredHeightLinear B G N z y =
      G.G z y.1 - G.G z (B.heightColumn z (controlSolution S B G N z y)) := by
  simp only [coupledRecoveredHeightLinear, LinearMap.sub_apply, LinearMap.comp_apply,
    coupledSourceLinear_apply, coupledControlSolutionLinear_apply, ContinuousLinearMap.coe_coe]

theorem coupledRecoveredHeightLinear_fst
    (B : ControlColumnData S) (G : ScalarInverseData S) (N : ControlInverseData S)
    (z : AnnularState S × ℝ) (y : ResidualSpace S) :
    (coupledRecoveredHeightLinear B G N z y).1 = (G.G z y.1).1 -
      controlHeightResponse S B G z (controlSolution S B G N z y) := by
  calc
    _ = (G.G z y.1 - G.G z (B.heightColumn z (controlSolution S B G N z y))).1 :=
      congrArg Prod.fst (coupledRecoveredHeightLinear_apply B G N z y)
    _ = (G.G z y.1).1 - (G.G z (B.heightColumn z (controlSolution S B G N z y))).1 := rfl
    _ = _ := congrArg ((G.G z y.1).1 - ·)
      (controlHeightResponse_apply B G z (controlSolution S B G N z y)).symm

def coupledRecoveryInputLinear (B : ControlColumnData S) (G : ScalarInverseData S)
    (N : ControlInverseData S) (z : AnnularState S × ℝ) :
    ResidualSpace S →ₗ[ℝ] CircleSpace S :=
  coupledCircleLinear S - z.2 • (B.heightRow z).toLinearMap.comp
    ((LinearMap.fst ℝ (HeightPair S) ℝ).comp (coupledRecoveredHeightLinear B G N z))

theorem coupledRecoveryInputLinear_apply
    (B : ControlColumnData S) (G : ScalarInverseData S) (N : ControlInverseData S)
    (z : AnnularState S × ℝ) (y : ResidualSpace S) :
    coupledRecoveryInputLinear B G N z y =
      y.2.val - z.2 • B.heightRow z (coupledRecoveredHeightLinear B G N z y).1 := by
  simp only [coupledRecoveryInputLinear, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.fst_apply, coupledCircleLinear_apply,
    ContinuousLinearMap.coe_coe]

def coupledRecoveredKappaLinear
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (B : ControlColumnData S) (G : ScalarInverseData S) (N : ControlInverseData S)
    (z : AnnularState S × ℝ) (hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m|) :
    ResidualSpace S →ₗ[ℝ] CircleSpace S :=
  (coupledInverseControlLift hS (B.diagonal z) hlo).toLinearMap.comp
    (coupledRecoveryInputLinear B G N z)

theorem coupledRecoveredKappaLinear_apply
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (B : ControlColumnData S) (G : ScalarInverseData S) (N : ControlInverseData S)
    (z : AnnularState S × ℝ) (hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m|)
    (y : ResidualSpace S) :
    coupledRecoveredKappaLinear hS B G N z hlo y =
      coupledInverseControlLift hS (B.diagonal z) hlo
        (coupledRecoveryInputLinear B G N z y) := rfl

def coupledRecoveryRemainderLinear
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (B : ControlColumnData S) (G : ScalarInverseData S) (N : ControlInverseData S)
    (z : AnnularState S × ℝ) (hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m|) :
    ResidualSpace S →ₗ[ℝ] CircleSpace S :=
  coupledRecoveryInputLinear B G N z - (B.circleColumn z).toLinearMap.comp
    (coupledRecoveredKappaLinear hS B G N z hlo)

theorem coupledRecoveryRemainderLinear_apply
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (B : ControlColumnData S) (G : ScalarInverseData S) (N : ControlInverseData S)
    (z : AnnularState S × ℝ) (hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m|)
    (y : ResidualSpace S) :
    coupledRecoveryRemainderLinear hS B G N z hlo y =
      y.2.val - z.2 • B.heightRow z (coupledRecoveredHeightLinear B G N z y).1 -
        B.circleColumn z (coupledRecoveredKappaLinear hS B G N z hlo y) := by
  simp only [coupledRecoveryRemainderLinear, LinearMap.sub_apply, LinearMap.comp_apply,
    coupledRecoveryInputLinear_apply, ContinuousLinearMap.coe_coe]

/-- The four columns are assembled by products of linear maps, so their
linearity is part of this definition rather than a subsequent assumption. -/
def coupledRecoveryLinear
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (R : ReturnEquationData S) (B : ControlColumnData S) (G : ScalarInverseData S)
    (N : ControlInverseData S) (z : AnnularState S × ℝ)
    (hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m|) :
    ResidualSpace S →ₗ[ℝ] AnnularState S :=
  ((LinearMap.fst ℝ (HeightPair S) ℝ).comp (coupledRecoveredHeightLinear B G N z)).prod
    (((LinearMap.snd ℝ (HeightPair S) ℝ).comp (coupledRecoveredHeightLinear B G N z)).prod
      ((coupledRecoveredKappaLinear hS B G N z hlo).prod
        ((R.chartIncrement z).comp
          (R.inverse.comp (coupledRecoveryRemainderLinear hS B G N z hlo)))))

theorem coupledRecoveryLinear_apply
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (R : ReturnEquationData S) (B : ControlColumnData S) (G : ScalarInverseData S)
    (N : ControlInverseData S) (z : AnnularState S × ℝ)
    (hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m|) (y : ResidualSpace S) :
    coupledRecoveryLinear hS R B G N z hlo y =
      ((coupledRecoveredHeightLinear B G N z y).1,
        ((coupledRecoveredHeightLinear B G N z y).2,
          (coupledRecoveredKappaLinear hS B G N z hlo y,
            R.chartIncrement z (R.inverse (coupledRecoveryRemainderLinear hS B G N z hlo y))))) := by
  simp only [coupledRecoveryLinear, LinearMap.prod_apply, Function.prod_apply,
    LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply]

private theorem linear_restriction_of_mean
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (L : E →ₗ[ℝ] F) (q : ℝ) (g h : E) (a : F)
    (he : a + q • L h = L g) : L (g - q • h) = a := by
  rw [L.map_sub, L.map_smul, ← he, add_sub_cancel_right]

/-- The control is recovered from its mean equation, rather than from an
unjustified extension of every base-space vector to the smooth circle space. -/
theorem coupledRecoveredKappaLinear_restriction
    (hS : IsCircleModel T (3 / 4 : ℝ) (S.circle (3 / 4 : ℝ)))
    (B : ControlColumnData S) (G : ScalarInverseData S) (N : ControlInverseData S)
    (z : AnnularState S × ℝ) (hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m|)
    (hrestriction : ∀ u m, B.restriction u m = T.H (T.sample m) ^ (-(3 / 4 : ℝ)) *
      angularMean ((S.circle (3 / 4 : ℝ)).decode u m))
    (hdiag : ∀ u m, B.J z u m = B.diagonal z m * u m)
    (hJ : ∀ u, B.JInverse z (B.J z u) = u ∧ B.J z (B.JInverse z u) = u)
    (hN : ∀ u, N.inverse z u - z.2 • controlFeedback S B G z (N.inverse z u) = u)
    (y : ResidualSpace S) :
    B.restriction (coupledRecoveredKappaLinear hS B G N z hlo y) =
      controlSolution S B G N z y := by
  have hη : (coupledRecoveredHeightLinear B G N z y).1 =
      (G.G z y.1).1 - controlHeightResponse S B G z (controlSolution S B G N z y) :=
    coupledRecoveredHeightLinear_fst B G N z y
  have hmean : B.J z (controlSolution S B G N z y) + z.2 •
      controlMeanRow S B z (coupledRecoveredHeightLinear B G N z y).1 = B.restriction y.2.val :=
    (congrArg (fun η => B.J z (controlSolution S B G N z y) +
      z.2 • controlMeanRow S B z η) hη).trans
        (controlSolution_mean_equation B G N z hN (fun u => (hJ u).2) y)
  have hinput : B.restriction (coupledRecoveryInputLinear B G N z y) =
      B.J z (controlSolution S B G N z y) := by
    have hm : B.J z (controlSolution S B G N z y) +
        z.2 • B.restriction (B.heightRow z (coupledRecoveredHeightLinear B G N z y).1) =
          B.restriction y.2.val :=
      (congrArg (fun a : ControlBanach => B.J z (controlSolution S B G N z y) + z.2 • a)
        (controlMeanRow_apply B z (coupledRecoveredHeightLinear B G N z y).1)).symm.trans hmean
    exact (congrArg (fun u : CircleSpace S => B.restriction u)
      (coupledRecoveryInputLinear_apply B G N z y)).trans
        (linear_restriction_of_mean B.restriction.toLinearMap z.2 y.2.val
          (B.heightRow z (coupledRecoveredHeightLinear B G N z y).1)
          (B.J z (controlSolution S B G N z y)) hm)
  have hlift := coupledInverseControlLift_restriction hS B z hrestriction hdiag
    (fun u => (hJ u).2) hlo (coupledRecoveryInputLinear B G N z y)
  exact (congrArg (fun u : CircleSpace S => B.restriction u)
    (coupledRecoveredKappaLinear_apply hS B G N z hlo y)).trans
      (hlift.trans ((congrArg (fun u : ControlBanach => B.JInverse z u) hinput).trans
        (hJ (controlSolution S B G N z y)).1))

/-- The pointwise equations of N09, written once for the recovered linear
map and for its total guarded representative. -/
def CoupledRecoveryEquations (S : PhysicalSpacesData) (R : ReturnEquationData S)
    (B : ControlColumnData S) (G : ScalarInverseData S) (N : ControlInverseData S)
    (z : AnnularState S × ℝ) (y : ResidualSpace S) (w : AnnularState S) : Prop :=
  let ξ := controlSolution S B G N z y
  let η := w.1
  let μ := w.2.1
  let κ := w.2.2.1
  let f := y.2.val - z.2 • B.heightRow z η - B.circleColumn z κ
  stateSector S w ∧ B.restriction κ = ξ ∧
    (η, μ) = G.G z y.1 - G.G z (B.heightColumn z ξ) ∧
    IsEvenZeroMeanCircle S f ∧
    w.2.2.2 = R.chartIncrement z (R.inverse f) ∧
    (S.circle (3 / 4 : ℝ)).decode (R.linearPart (R.inverse f)) =
      (S.circle (3 / 4 : ℝ)).decode f

theorem coupledRecoveryLinear_equations
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {G : ScalarInverseData S} {P : ResidualData S} {B : ControlColumnData S}
    {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (N : ControlInverseData S) {z : AnnularState S × ℝ}
    (hz : z ∈ stateNeighborhood S C base ε) (hs : stateSector S z.1)
    (hlo : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m|)
    (hN : ∀ u, N.inverse z u - z.2 • controlFeedback S B G z (N.inverse z u) = u)
    (y : ResidualSpace S) :
    CoupledRecoveryEquations S R B G N z y
      (coupledRecoveryLinear (hS.2.1 (3 / 4 : ℝ)) R B G N z hlo y) := by
  have hrestriction := h8.2.2.2.2.2.1
  have hcolumn := h8.2.2.2.2.2.2.2.2.2.2.2.1
  have hdiag := h8.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hJ := h8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  let hM := hS.2.1 (3 / 4 : ℝ)
  let η := (coupledRecoveredHeightLinear B G N z y).1
  let μ : ℝ := (coupledRecoveredHeightLinear B G N z y).2
  let κ := coupledRecoveredKappaLinear hM B G N z hlo y
  let f := y.2.val - z.2 • B.heightRow z η - B.circleColumn z κ
  have hκ : B.restriction κ = controlSolution S B G N z y :=
    coupledRecoveredKappaLinear_restriction hM B G N z hlo hrestriction
      (hdiag z hz hs) (hJ z hz hs) hN y
  have hη : η = (G.G z y.1).1 -
      controlHeightResponse S B G z (controlSolution S B G N z y) :=
    coupledRecoveredHeightLinear_fst B G N z y
  have hmean : B.restriction f = 0 :=
    controlSolution_restriction_remainder B G N z hN (fun u => (hJ z hz hs u).2)
      (hcolumn z hz hs) y η κ hη hκ
  have hH (m : ℕ) : 0 < T.H (T.sample m) :=
    (hT.2.1 _ (materialSample_mem_radialCore hT h1.1.1.choose_spec.2.1 m)).2.1
  have hf : IsEvenZeroMeanCircle S f :=
    coupled_circleRemainder_even_zeroMean hS h8 hH hz hs y η κ hmean
  have hinverse := h2.2.2.2.2.2.2.2.1 f hf
  have hchart : IsOddCircle S (R.chartIncrement z (R.inverse f)) :=
    coupled_chartIncrement_isOdd h1 h2 hz hs hinverse.2
  have hκconstant : ∀ m θ φ, (S.circle (3 / 4 : ℝ)).decode κ m θ =
      (S.circle (3 / 4 : ℝ)).decode κ m φ := by
    intro m θ φ
    have he := coupledRecoveredKappaLinear_apply hM B G N z hlo y
    exact (congrArg (fun q => (S.circle (3 / 4 : ℝ)).decode q m θ) he).trans
      ((coupledInverseControlLift_constant hM (B.diagonal z) hlo
        (coupledRecoveryInputLinear B G N z y) m θ φ).trans
          (congrArg (fun q => (S.circle (3 / 4 : ℝ)).decode q m φ) he).symm)
  have hpoint : CoupledRecoveryEquations S R B G N z y
      (η, (μ, (κ, R.chartIncrement z (R.inverse f)))) :=
    ⟨⟨hκconstant, hchart⟩, hκ, coupledRecoveredHeightLinear_apply B G N z y,
      hf, rfl, congrArg (S.circle (3 / 4 : ℝ)).decode hinverse.1⟩
  have he : coupledRecoveryLinear hM R B G N z hlo y =
      (η, (μ, (κ, R.chartIncrement z (R.inverse f)))) :=
    (coupledRecoveryLinear_apply hM R B G N z hlo y).trans
      (congrArg (fun u : CircleSpace S => (η, (μ, (κ, R.chartIncrement z (R.inverse u)))))
        (coupledRecoveryRemainderLinear_apply hM B G N z hlo y))
  exact he.symm ▸ hpoint

section TotalRepresentative

variable {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {G : ScalarInverseData S} {P : ResidualData S} {B : ControlColumnData S}
  {base loss : ℕ} {ε : ℝ}

def CoupledRecoveryValid (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
    (B : ControlColumnData S) (G : ScalarInverseData S) (base : ℕ) (ε : ℝ)
    (z : AnnularState S × ℝ) : Prop :=
  z ∈ stateNeighborhood S C base ε ∧ stateSector S z.1 ∧
    ‖z.2 • controlFeedback S B G z‖ < (1 / 2 : ℝ)

theorem coupledRecovery_diagonal_lower
    (h8 : N08Properties D T S C R G P B base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) : ∀ m, (1 / 2 : ℝ) ≤ |B.diagonal z m| := by
  intro m
  exact (h8.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 z hz hs m).1

/-- A globally defined linear map in the source, with the actual recovery
on the valid sector and zero elsewhere. -/
def coupledRecoveredV (hS : IsPhysicalSpaces D T S)
    (h8 : N08Properties D T S C R G P B base loss ε) :
    AnnularState S × ℝ → ResidualSpace S →ₗ[ℝ] AnnularState S := by
  classical
  exact fun z => if hz : CoupledRecoveryValid S C B G base ε z then
    coupledRecoveryLinear (hS.2.1 (3 / 4 : ℝ)) R B G (coupledControlInverse S B G) z
      (coupledRecovery_diagonal_lower h8 hz.1 hz.2.1)
    else 0

theorem coupledRecoveredV_eq (hS : IsPhysicalSpaces D T S)
    (h8 : N08Properties D T S C R G P B base loss ε)
    {z : AnnularState S × ℝ} (hz : CoupledRecoveryValid S C B G base ε z) :
    coupledRecoveredV hS h8 z =
      coupledRecoveryLinear (hS.2.1 (3 / 4 : ℝ)) R B G (coupledControlInverse S B G) z
        (coupledRecovery_diagonal_lower h8 hz.1 hz.2.1) := by
  simp only [coupledRecoveredV, dif_pos hz]

theorem coupledRecoveredV_equations
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    {z : AnnularState S × ℝ} (hz : CoupledRecoveryValid S C B G base ε z)
    (y : ResidualSpace S) :
    CoupledRecoveryEquations S R B G (coupledControlInverse S B G) z y
      (coupledRecoveredV hS h8 z y) := by
  have hlin := coupledRecoveryLinear_equations hT hS h1 h2 h8
    (coupledControlInverse S B G) hz.1 hz.2.1
    (coupledRecovery_diagonal_lower h8 hz.1 hz.2.1)
    (coupledControlInverse_right B G z hz.2.2) y
  have he := congrArg (fun L : ResidualSpace S →ₗ[ℝ] AnnularState S => L y)
    (coupledRecoveredV_eq hS h8 hz)
  exact he.symm ▸ hlin

theorem coupledRecoveredV_sector
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (z : AnnularState S × ℝ) (y : ResidualSpace S) :
    stateSector S (coupledRecoveredV hS h8 z y) := by
  classical
  by_cases hz : CoupledRecoveryValid S C B G base ε z
  · exact (coupledRecoveredV_equations hT hS h1 h2 h8 hz y).1
  · simp only [coupledRecoveredV, dif_neg hz, LinearMap.zero_apply]
    exact (stateSectorSubmodule S).zero_mem

/-- Both fields are the very same linear recovery, with the second one
restricted to its proved sector-valued range. -/
def coupledRecoveredInverseData
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    (h8 : N08Properties D T S C R G P B base loss ε) : CoupledInverseData S where
  V := coupledRecoveredV hS h8
  sectorV z := (coupledRecoveredV hS h8 (liftSectorParameter S C z)).codRestrict
    (stateSectorSubmodule S)
    (coupledRecoveredV_sector hT hS h1 h2 h8 (liftSectorParameter S C z))

theorem coupledRecoveredInverseData_sectorV
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (z : StateDirections S × ℝ) (y : ResidualSpace S) :
    ((coupledRecoveredInverseData hT hS h1 h2 h8).sectorV z y).val =
      (coupledRecoveredInverseData hT hS h1 h2 h8).V (liftSectorParameter S C z) y := rfl

/-- On any smaller parameter strip satisfying the actual Neumann bound,
the complete recovery clause of N09 holds for this candidate. -/
theorem coupledRecoveredInverseData_recovery
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    (h8 : N08Properties D T S C R G P B base loss ε)
    {q0 : ℝ} (hq0 : q0 ≤ ε)
    (hsmall : ∀ z ∈ coupledNeighborhood S C base ε q0, stateSector S z.1 →
      ‖z.2 • controlFeedback S B G z‖ < (1 / 2 : ℝ))
    {z : AnnularState S × ℝ} (hz : z ∈ coupledNeighborhood S C base ε q0)
    (hs : stateSector S z.1) (y : ResidualSpace S) :
    CoupledRecoveryEquations S R B G (coupledControlInverse S B G) z y
      ((coupledRecoveredInverseData hT hS h1 h2 h8).V z y) := by
  have hvalid : CoupledRecoveryValid S C B G base ε z :=
    ⟨⟨hz.1, hz.2.trans_le hq0⟩, hs, hsmall z hz hs⟩
  exact coupledRecoveredV_equations hT hS h1 h2 h8 hvalid y

end TotalRepresentative

end ContinuousFlexibility.Statements
