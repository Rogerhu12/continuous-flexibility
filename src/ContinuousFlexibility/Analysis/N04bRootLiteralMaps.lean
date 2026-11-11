import ContinuousFlexibility.Analysis.RootCharacteristicFactor
import ContinuousFlexibility.Analysis.N04bCollarInverseGluing
import ContinuousFlexibility.Geometry.PlanarOrientation

/-!
# Literal physical maps pasted at either root

One affine homeomorphism sends the physical radial variable to its inward
root coordinate. The actual physical chart and height are retained on the
positive side. On the other side they use the smooth extended root model.
The inverse retains the actual physical inverse at positive canonical
radius and uses the physical affine image of the collar inverse otherwise.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open scoped Topology ContDiff

/-- Physical coordinates to inward root coordinates; its inverse is the
already defined actual root profile shift. -/
def n04bRootAffine (r₀ : ℝ) (side : Bool) : PolarPoint ≃ₜ PolarPoint where
  toFun p := (if side then r₀ - p.1 else p.1 - r₀, p.2)
  invFun := rootProfileShift r₀ (if side then -1 else 1)
  left_inv := by
    intro p
    cases side <;> apply Prod.ext <;> simp [rootProfileShift] <;> ring
  right_inv := by
    intro p
    cases side <;> apply Prod.ext <;> simp [rootProfileShift] <;> ring
  continuous_toFun := by
    cases side with
    | false => exact (continuous_fst.sub continuous_const).prodMk continuous_snd
    | true => exact (continuous_const.sub continuous_fst).prodMk continuous_snd
  continuous_invFun :=
    (continuous_const.add (continuous_const.mul continuous_fst)).prodMk continuous_snd

theorem n04bRootAffine_apply (r₀ : ℝ) (side : Bool) (p : PolarPoint) :
    n04bRootAffine r₀ side p =
      (if side then r₀ - p.1 else p.1 - r₀, p.2) := rfl

theorem n04bRootAffine_symm_apply (r₀ : ℝ) (side : Bool) (p : PolarPoint) :
    (n04bRootAffine r₀ side).symm p =
      rootProfileShift r₀ (if side then -1 else 1) p := rfl

theorem n04bRootAffine_at_root (r₀ : ℝ) (side : Bool) (θ : ℝ) :
    n04bRootAffine r₀ side (r₀, θ) = (0, θ) := by
  cases side <;> simp [n04bRootAffine_apply]

theorem n04bRootAffine_contDiff (r₀ : ℝ) (side : Bool) :
    ContDiff ℝ ∞ (n04bRootAffine r₀ side : PolarPoint → PolarPoint) := by
  cases side with
  | false => exact (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
  | true => exact (contDiff_const.sub contDiff_fst).prodMk contDiff_snd

theorem n04bRootAffine_symm_contDiff (r₀ : ℝ) (side : Bool) :
    ContDiff ℝ ∞ ((n04bRootAffine r₀ side).symm : PolarPoint → PolarPoint) :=
  (contDiff_const.add (contDiff_const.mul contDiff_fst)).prodMk contDiff_snd

theorem n04bRootAffine_jacobian_ne_zero
    (r₀ : ℝ) (side : Bool) (p : PolarPoint) :
    planeJacobian (n04bRootAffine r₀ side : PolarPoint → PolarPoint) p ≠ 0 :=
  planeJacobian_ne_zero_of_homeomorph_smooth_inverse (n04bRootAffine r₀ side)
    ((n04bRootAffine_contDiff r₀ side).differentiable (by simp) p)
    ((n04bRootAffine_symm_contDiff r₀ side).differentiable (by simp)
      (n04bRootAffine r₀ side p))

def n04bPastedRootChart (r₀ : ℝ) (side : Bool)
    (Froot Fphysical : PolarPoint → PolarPoint) (p : PolarPoint) : PolarPoint :=
  if 0 < (n04bRootAffine r₀ side p).1 then Fphysical p
  else Froot (n04bRootAffine r₀ side p)

def n04bPastedRootHeight (r₀ : ℝ) (side : Bool)
    (hroot hphysical : PolarPoint → ℝ) (p : PolarPoint) : ℝ :=
  if 0 < (n04bRootAffine r₀ side p).1 then hphysical p
  else hroot (n04bRootAffine r₀ side p)

def n04bPastedRootInverse (r₀ : ℝ) (side : Bool)
    (Gcollar Xphysical : PolarPoint → PolarPoint) : PolarPoint → PolarPoint :=
  n04bGluedRootInverse
    (fun q => (n04bRootAffine r₀ side).symm (Gcollar q)) Xphysical

/-- A single value-level pasting lemma applies to both charts and heights. -/
theorem n04b_rootSidePaste_eqOn
    {E : Type*} (e : PolarPoint ≃ₜ PolarPoint)
    {froot fphysical : PolarPoint → E} {S : Set PolarPoint}
    (hMatch : EqOn (fun q => fphysical (e.symm q)) froot
      (S ∩ {q : PolarPoint | 0 < q.1})) :
    EqOn (fun p => if 0 < (e p).1 then fphysical p else froot (e p))
      (fun p => froot (e p)) (e ⁻¹' S) := by
  intro p hp
  by_cases hpos : 0 < (e p).1
  · rw [if_pos hpos]
    simpa only [Homeomorph.symm_apply_apply] using hMatch ⟨hp, hpos⟩
  · exact if_neg hpos

theorem n04b_rootSidePaste_germ
    {E : Type*} (e : PolarPoint ≃ₜ PolarPoint)
    {froot fphysical : PolarPoint → E} {S : Set PolarPoint} {p : PolarPoint}
    (hS : IsOpen S) (hp : e p ∈ S)
    (hMatch : EqOn (fun q => fphysical (e.symm q)) froot
      (S ∩ {q : PolarPoint | 0 < q.1})) :
    (fun q => if 0 < (e q).1 then fphysical q else froot (e q)) =ᶠ[𝓝 p]
      (fun q => froot (e q)) := by
  filter_upwards [(hS.preimage e.continuous).mem_nhds hp] with q hq
  exact n04b_rootSidePaste_eqOn e hMatch hq

theorem n04b_rootSidePaste_physical_germ
    {E : Type*} (e : PolarPoint ≃ₜ PolarPoint)
    (froot fphysical : PolarPoint → E) {p : PolarPoint}
    (hp : 0 < (e p).1) :
    (fun q => if 0 < (e q).1 then fphysical q else froot (e q)) =ᶠ[𝓝 p] fphysical := by
  filter_upwards [(isOpen_lt continuous_const e.continuous.fst).mem_nhds hp] with q hq
  exact if_pos hq

theorem n04bPastedRootChart_physical_germ
    (r₀ : ℝ) (side : Bool) (Froot Fphysical : PolarPoint → PolarPoint)
    {p : PolarPoint} (hp : 0 < (n04bRootAffine r₀ side p).1) :
    n04bPastedRootChart r₀ side Froot Fphysical =ᶠ[𝓝 p] Fphysical :=
  n04b_rootSidePaste_physical_germ (n04bRootAffine r₀ side) Froot Fphysical hp

theorem n04bPastedRootHeight_physical_germ
    (r₀ : ℝ) (side : Bool) (hroot hphysical : PolarPoint → ℝ)
    {p : PolarPoint} (hp : 0 < (n04bRootAffine r₀ side p).1) :
    n04bPastedRootHeight r₀ side hroot hphysical =ᶠ[𝓝 p] hphysical :=
  n04b_rootSidePaste_physical_germ (n04bRootAffine r₀ side) hroot hphysical hp

theorem n04bPastedRootInverse_physical_germ
    (r₀ : ℝ) (side : Bool) (Gcollar Xphysical : PolarPoint → PolarPoint)
    {q : PolarPoint} (hq : 0 < q.1) :
    n04bPastedRootInverse r₀ side Gcollar Xphysical =ᶠ[𝓝 q] Xphysical :=
  n04bGluedRootInverse_physical_germ _ _ hq

end ContinuousFlexibility.Analysis
