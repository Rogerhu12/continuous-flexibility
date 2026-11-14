module

public import ContinuousFlexibility.Analysis.CoupledControlAlgebra
public import ContinuousFlexibility.Analysis.SolveResidualSpaces
public import ContinuousFlexibility.Analysis.SolveTameSubspace
public import ContinuousFlexibility.Analysis.NeighborhoodCircleChartsState

/-!
# Parity of the actual circle columns and the recovered chart

The circle residual already has values in the closed even subspace. Its
genuine directional derivatives therefore remain in that same subspace.
This supplies the parity of both columns used in the coupled elimination.
The zero-mean inverse and the odd left chart then supply the chart sector.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set ContinuousFlexibility.Analysis

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}

theorem coupled_circleLineDeriv_mem_even
    (hS : IsPhysicalSpaces D T S) (F : AnnularState S → EvenCircle S)
    {x v : AnnularState S} {d : CircleSpace S}
    (hd : HasProjectiveLineDerivAt (fun y => (F y).val) d x v) :
    d ∈ evenCircleSubmodule S :=
  solve_lineDeriv_mem_submodule (evenCircleSubmodule S)
    (solve_isClosed_evenCircle hS) isOpen_univ
    (fun y _ => (F y).property) (mem_univ x) hd

variable {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {G : ScalarInverseData S} {P : ResidualData S} {B : ControlColumnData S}
  {base loss : ℕ} {ε : ℝ}

theorem coupled_heightRow_mem_even
    (hS : IsPhysicalSpaces D T S)
    (h8 : N08Properties D T S C R G P B base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (η : HeightPair S) :
    z.2 • B.heightRow z η ∈ evenCircleSubmodule S := by
  apply coupled_circleLineDeriv_mem_even hS (fun x => P.circle (x, z.2))
  exact h8.2.2.2.2.2.2.2.2.2.1 z hz hs η

theorem coupled_circleColumn_mem_even
    (hS : IsPhysicalSpaces D T S)
    (h8 : N08Properties D T S C R G P B base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (κ : CircleSpace S) :
    B.circleColumn z κ ∈ evenCircleSubmodule S := by
  apply coupled_circleLineDeriv_mem_even hS (fun x => P.circle (x, z.2))
  exact h8.2.2.2.2.2.2.2.2.2.2.1 z hz hs κ

theorem coupled_circleRemainder_even
    (hS : IsPhysicalSpaces D T S)
    (h8 : N08Properties D T S C R G P B base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (y : ResidualSpace S)
    (η : HeightPair S) (κ : CircleSpace S) :
    y.2.val - z.2 • B.heightRow z η - B.circleColumn z κ ∈ evenCircleSubmodule S :=
  (evenCircleSubmodule S).sub_mem
    ((evenCircleSubmodule S).sub_mem y.2.property
      (coupled_heightRow_mem_even hS h8 hz hs η))
    (coupled_circleColumn_mem_even hS h8 hz hs κ)

/-- Mean cancellation and the actual even column derivatives give the
precise domain of the N02 small-divisor inverse. -/
theorem coupled_circleRemainder_even_zeroMean
    (hS : IsPhysicalSpaces D T S)
    (h8 : N08Properties D T S C R G P B base loss ε)
    (hH : ∀ m, 0 < T.H (T.sample m))
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (y : ResidualSpace S)
    (η : HeightPair S) (κ : CircleSpace S)
    (hmean : B.restriction (y.2.val - z.2 • B.heightRow z η - B.circleColumn z κ) = 0) :
    IsEvenZeroMeanCircle S (y.2.val - z.2 • B.heightRow z η - B.circleColumn z κ) := by
  have heven := coupled_circleRemainder_even hS h8 hz hs y η κ
  intro m
  exact ⟨fun θ => heven m θ,
    controlRestriction_mean_zero B h8.2.2.2.2.2.1 hH hmean m⟩

/-- The composition prescribed by N02 preserves oddness because the
actual left chart lies in the odd sector. -/
theorem coupled_chartIncrement_isOdd
    (h1 : N01Properties D T S C base loss ε)
    (h2 : N02Properties D T S C R base ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {v : CircleSpace S} (hv : IsOddCircle S v) :
    IsOddCircle S (R.chartIncrement z v) := by
  intro m θ
  calc
    _ = (S.circle (3 / 4 : ℝ)).decode v m (stateLeftChart S z.1 m (-θ)) :=
      h2.2.2.2.2.2.1 z hz hs v m (-θ)
    _ = (S.circle (3 / 4 : ℝ)).decode v m (-stateLeftChart S z.1 m θ) :=
      congrArg ((S.circle (3 / 4 : ℝ)).decode v m) (stateLeftChart_odd hs m θ)
    _ = -(S.circle (3 / 4 : ℝ)).decode v m (stateLeftChart S z.1 m θ) :=
      hv m (stateLeftChart S z.1 m θ)
    _ = _ := congrArg Neg.neg (h2.2.2.2.2.2.1 z hz hs v m θ).symm

end ContinuousFlexibility.Statements
