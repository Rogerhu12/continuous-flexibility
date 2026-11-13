import ContinuousFlexibility.Analysis.N04NegativeHeightGerms
import ContinuousFlexibility.Analysis.N04NegativeHeightScalarData

/-!
# Square roots of normalized current families

Both scalar kernels are evaluated on the same fixed compact positive
interval, after a single uniform shrink. Their reference value is one.
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

def n04NegativeHeightSqrtFactor (inverse : Bool) (x : ℝ) : ℝ :=
  if inverse then (Real.sqrt x)⁻¹ else Real.sqrt x

theorem n04NegativeHeightSqrtFactor_one (inverse : Bool) :
    n04NegativeHeightSqrtFactor inverse 1 = 1 := by
  cases inverse <;> simp [n04NegativeHeightSqrtFactor]

theorem n04NegativeHeightSqrtFactor_smooth (inverse : Bool) :
    ContDiffOn ℝ ∞ (n04NegativeHeightSqrtFactor inverse) (Ioi (0 : ℝ)) := by
  intro x hx
  have hs : ContDiffAt ℝ ∞ (fun t : ℝ => Real.sqrt t) x :=
    contDiffAt_id.sqrt hx.ne'
  cases inverse with
  | false => exact hs.contDiffWithinAt
  | true => exact (hs.inv (Real.sqrt_pos.mpr hx).ne').contDiffWithinAt

namespace N04HeightCurrentGerm

variable {S : PhysicalSpacesData} {T : MaterialData} {D : ReferenceData}
  {cell : ℕ → ℕ} {P : ℕ → Prop} {base : ℕ} {ε : ℝ}
  {f : Parameter S → ℕ → PolarPoint → ℝ} {f₀ : ℕ → PolarPoint → ℝ}

theorem sqrtFactor
    (hf : N04HeightCurrentGerm S T cell P base ε f f₀)
    (hD : IsAccumulatingProfile D) (hT : IsMaterialData D T)
    (hI : HasInterpolation (parameterGrading S))
    (hE : ∀ m, 1 ≤ T.E0 (T.sample (cell m)))
    (hone : ∀ m, P m → ∀ q ∈ unitStrip, f₀ m q = 1)
    (inverse : Bool) :
    N04HeightCurrentGerm S T cell P base ε
      (fun z m q => n04NegativeHeightSqrtFactor inverse (f z m q)) (fun _ _ => 1) := by
  obtain ⟨b₁, ε₁, hb₁, he₁, hele₁, hd⟩ := hf.2.2
  obtain ⟨b₂, ε₂, hb₂, he₂, hele₂, hd₂, hrange⟩ :=
    hd.height_range_one hD hT he₁ hE hone
  have hKV : Icc (1 / 2 : ℝ) (3 / 2 : ℝ) ⊆ Ioi (0 : ℝ) := by
    intro x hx
    linarith [hx.1]
  obtain ⟨b₃, ε₃, hb₃, he₃, hele₃, hcomp⟩ :=
    hd₂.height_scalarComp hD hT hI he₂ hE hf.1 hf.2.1 isOpen_Ioi
      isCompact_Icc hKV (n04NegativeHeightSqrtFactor inverse)
      (n04NegativeHeightSqrtFactor_smooth inverse) hrange
  have href : N04HeightReferenceDataOn T cell P (fun _ _ => (1 : ℝ)) :=
    n04HeightReferenceDataOn_pieceConstant (fun _ => 1) hE
      ⟨1, zero_lt_one, fun m _ => by simpa only [abs_one, Real.rpow_one, one_mul] using hE m⟩
  have heqref (m : ℕ) (hm : P m) (q : PolarPoint) (hq : q ∈ unitStrip) :
      n04NegativeHeightSqrtFactor inverse (f₀ m q) = 1 := by
    rw [hone m hm q hq, n04NegativeHeightSqrtFactor_one]
  exact ⟨href, fun m hm q hq =>
      (congrArg (n04NegativeHeightSqrtFactor inverse) (hf.2.1 m hm hq)).trans
        (heqref m hm q hq),
    b₃, ε₃, hb₁.trans (hb₂.trans hb₃), he₃, hele₃.trans (hele₂.trans hele₁),
    hcomp.height_congr (fun _ _ _ _ _ _ => rfl) (fun m hm q hq => heqref m hm q hq)⟩

end N04HeightCurrentGerm

end ContinuousFlexibility.Analysis
