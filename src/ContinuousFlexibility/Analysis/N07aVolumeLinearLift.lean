import ContinuousFlexibility.Analysis.N07aVolumeCell
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Linear realization in a prescribed source level

Existence in the actual volume graph and injectivity of its forget map
determine the lift uniquely.  The standard range equivalence supplies
linearity; the genuine norm estimate then supplies continuity.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
  {V : VolumeModelData S K}

local instance n07aVolumeLinearLiftLevelGroup (γ t : ℝ) (s : ℕ) :
    NormedAddCommGroup (V.level γ t s) := Submodule.normedAddCommGroup _
local instance n07aVolumeLinearLiftLevelSpace (γ t : ℝ) (s : ℕ) :
    NormedSpace ℝ (V.level γ t s) := Submodule.normedSpace _

def n07aVolumeLinearLift (hV : IsVolumeModel T S K V) (γ t : ℝ) (s : ℕ)
    (f : E →ₗ[ℝ] CanonicalSequence S K)
    (hf : ∀ x, ∃ W : V.level γ t s, V.forget γ t s W = f x) : E →ₗ[ℝ] V.level γ t s :=
  (LinearEquiv.ofInjective (V.forget γ t s) (hV.2.2.1 γ t s)).symm.toLinearMap.comp
    (f.codRestrict (V.forget γ t s).range hf)

theorem n07aVolumeLinearLift_forget (hV : IsVolumeModel T S K V) (γ t : ℝ) (s : ℕ)
    (f : E →ₗ[ℝ] CanonicalSequence S K)
    (hf : ∀ x, ∃ W : V.level γ t s, V.forget γ t s W = f x) (x : E) :
    V.forget γ t s (n07aVolumeLinearLift hV γ t s f hf x) = f x := by
  rw [n07aVolumeLinearLift, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [LinearEquiv.ofInjective_symm_apply, LinearMap.codRestrict_apply]

theorem n07aVolumeLinearLift_eq (hV : IsVolumeModel T S K V) (γ t : ℝ) (s : ℕ)
    (f : E →ₗ[ℝ] CanonicalSequence S K)
    (hf : ∀ x, ∃ W : V.level γ t s, V.forget γ t s W = f x)
    (x : E) (W : V.level γ t s) (hW : V.forget γ t s W = f x) :
    n07aVolumeLinearLift hV γ t s f hf x = W :=
  (hV.2.2.1 γ t s) ((n07aVolumeLinearLift_forget hV γ t s f hf x).trans hW.symm)

def n07aVolumeBoundedLift (hV : IsVolumeModel T S K V) (γ t : ℝ) (s : ℕ)
    (f : E →ₗ[ℝ] CanonicalSequence S K) (A : ℝ)
    (hf : ∀ x, ∃ W : V.level γ t s, V.forget γ t s W = f x ∧ ‖W‖ ≤ A * ‖x‖) :
    E →L[ℝ] V.level γ t s :=
  (n07aVolumeLinearLift hV γ t s f (fun x => (hf x).imp fun W hW => hW.1)).mkContinuous A
    (fun x => by
      obtain ⟨W, hW, hb⟩ := hf x
      rw [n07aVolumeLinearLift_eq hV γ t s f _ x W hW]
      exact hb)

theorem n07aVolumeBoundedLift_forget (hV : IsVolumeModel T S K V) (γ t : ℝ) (s : ℕ)
    (f : E →ₗ[ℝ] CanonicalSequence S K) (A : ℝ)
    (hf : ∀ x, ∃ W : V.level γ t s, V.forget γ t s W = f x ∧ ‖W‖ ≤ A * ‖x‖)
    (x : E) : V.forget γ t s (n07aVolumeBoundedLift hV γ t s f A hf x) = f x := by
  rw [n07aVolumeBoundedLift, LinearMap.mkContinuous_apply]
  exact n07aVolumeLinearLift_forget hV γ t s f _ x

theorem n07aVolumeBoundedLift_norm_le (hV : IsVolumeModel T S K V) (γ t : ℝ) (s : ℕ)
    (f : E →ₗ[ℝ] CanonicalSequence S K) (A : ℝ)
    (hf : ∀ x, ∃ W : V.level γ t s, V.forget γ t s W = f x ∧ ‖W‖ ≤ A * ‖x‖)
    (x : E) : ‖n07aVolumeBoundedLift hV γ t s f A hf x‖ ≤ A * ‖x‖ := by
  obtain ⟨W, hW, hb⟩ := hf x
  have he : n07aVolumeBoundedLift hV γ t s f A hf x = W :=
    (hV.2.2.1 γ t s) ((n07aVolumeBoundedLift_forget hV γ t s f A hf x).trans hW.symm)
  rwa [he]

end ContinuousFlexibility.Analysis
