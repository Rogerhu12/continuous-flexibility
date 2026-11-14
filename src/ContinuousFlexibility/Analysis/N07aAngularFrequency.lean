module

public import ContinuousFlexibility.Analysis.N07aAngularHilbert
public import ContinuousFlexibility.Analysis.AngularYosida

/-!
# The actual nonnegative angular-frequency operator

The operator acts within the real even source graph. Its Fourier symbol
is `|jθ|`; since the angular period is `π`, the physical symbol of
`|∂θ|` is twice this one. This fixes the normalization used when applying
the existing real angular inverse theorem.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

variable {T : MaterialData} {S : PhysicalSpacesData} {K : CanonicalData S}
  {V : VolumeModelData S K}
  (hV : IsVolumeModel T S K V) (γ w : ℝ)
  (hK : ∀ m, K.left m < K.right m) (b : ℕ)

local instance n07aFrequencyLevelGroup : NormedAddCommGroup (V.level γ w b) := Submodule.normedAddCommGroup _
local instance n07aFrequencyLevelSpace : NormedSpace ℝ (V.level γ w b) := Submodule.normedSpace _
local instance n07aFrequencyLevelInner : InnerProductSpace ℝ (V.level γ w b) := Submodule.innerProductSpace _
local instance n07aFrequencyBandGroup (n : ℕ) : NormedAddCommGroup (n07aAngularBandSpace hV γ w hK b n) :=
  Submodule.normedAddCommGroup _
local instance n07aFrequencyBandSpace (n : ℕ) : NormedSpace ℝ (n07aAngularBandSpace hV γ w hK b n) :=
  Submodule.normedSpace _
local instance n07aFrequencyBandInner (n : ℕ) : InnerProductSpace ℝ (n07aAngularBandSpace hV γ w hK b n) :=
  Submodule.innerProductSpace _
local instance n07aFrequencyLpGroup : NormedAddCommGroup
    (lp (fun n => n07aAngularBandSpace hV γ w hK b n) 2) := lp.normedAddCommGroup
local instance n07aFrequencyLpSpace : NormedSpace ℝ
    (lp (fun n => n07aAngularBandSpace hV γ w hK b n) 2) := lp.instNormedSpace
local instance n07aFrequencyLpInner : InnerProductSpace ℝ
    (lp (fun n => n07aAngularBandSpace hV γ w hK b n) 2) := lp.instInnerProductSpace

def n07aAngularLambda (u : V.level γ w b) : V.level γ w b :=
  (n07aAngularHilbertEquiv hV γ w hK b).symm
    (angularDerivative (𝕜 := ℝ) (n07aAngularHilbertEquiv hV γ w hK b u))

theorem n07aAngularLambda_coordinates (u : V.level γ w b) :
    n07aAngularHilbertEquiv hV γ w hK b (n07aAngularLambda hV γ w hK b u) =
      angularDerivative (𝕜 := ℝ) (n07aAngularHilbertEquiv hV γ w hK b u) :=
  LinearIsometryEquiv.apply_symm_apply _ _

theorem n07aAngularLambda_band (u : V.level γ w b)
    (hu : n07aAngularHilbertEquiv hV γ w hK b u ∈ angularFrequencyDomain (𝕜 := ℝ)) (n : ℕ) :
    n07aAngularLevelBand hV γ w hK b n (n07aAngularLambda hV γ w hK b u) =
      (n : ℝ) • n07aAngularLevelBand hV γ w hK b n u := by
  calc
    n07aAngularLevelBand hV γ w hK b n (n07aAngularLambda hV γ w hK b u) =
        (n07aAngularHilbertEquiv hV γ w hK b (n07aAngularLambda hV γ w hK b u) n).val :=
      (n07aAngularHilbertEquiv_apply_val hV γ w hK b _ n).symm
    _ = (angularDerivative (𝕜 := ℝ) (n07aAngularHilbertEquiv hV γ w hK b u) n).val :=
      congrArg (fun v : lp (fun n => n07aAngularBandSpace hV γ w hK b n) 2 => (v n).val)
        (n07aAngularLambda_coordinates hV γ w hK b u)
    _ = (n : ℝ) • (n07aAngularHilbertEquiv hV γ w hK b u n).val := by
      have hd := congrArg (fun v : n07aAngularBandSpace hV γ w hK b n => v.val)
        (angularDerivative_apply (𝕜 := ℝ)
          (E := fun n => n07aAngularBandSpace hV γ w hK b n)
          (v := n07aAngularHilbertEquiv hV γ w hK b u) hu n)
      simpa only [RCLike.ofReal_real_eq_id, id_eq, Submodule.coe_smul] using hd
    _ = _ := congrArg (fun v : V.level γ w b => (n : ℝ) • v)
      (n07aAngularHilbertEquiv_apply_val hV γ w hK b u n)

theorem n07aAngularLambda_fourier (u : V.level γ w b)
    (hu : n07aAngularHilbertEquiv hV γ w hK b u ∈ angularFrequencyDomain (𝕜 := ℝ))
    (m : ℕ) (k : Fin (b + 1)) (j : SpacesTorusFrequency) :
    n07aAngularFourier m (hK m) ((n07aAngularLambda hV γ w hK b u).val m k) j =
      (n07aAngularFrequency j : ℂ) * n07aAngularFourier m (hK m) (u.val m k) j := by
  have h := congrArg
    (fun v : V.level γ w b => n07aAngularFourier m (hK m) (v.val m k) j)
    (n07aAngularLambda_band hV γ w hK b u hu (n07aAngularFrequency j))
  simpa only [n07aAngularLevelBand_apply, n07aAngularBand_coefficient, ite_true,
    Submodule.coe_smul, lp.coeFn_smul, Pi.smul_apply, PiLp.smul_apply, map_smul,
    Complex.real_smul, Complex.ofReal_natCast] using h

theorem n07aAngularLambda_norm_le (u : V.level γ w b)
    (hu : MemAngularSobolev (𝕜 := ℝ) 1 (n07aAngularHilbertEquiv hV γ w hK b u)) :
    ‖n07aAngularLambda hV γ w hK b u‖ ≤
      angularSobolevNorm (𝕜 := ℝ) 1 (n07aAngularHilbertEquiv hV γ w hK b u) := by
  calc
    ‖n07aAngularLambda hV γ w hK b u‖ =
        ‖n07aAngularHilbertEquiv hV γ w hK b (n07aAngularLambda hV γ w hK b u)‖ :=
      ((n07aAngularHilbertEquiv hV γ w hK b).norm_map _).symm
    _ = ‖angularDerivative (𝕜 := ℝ) (n07aAngularHilbertEquiv hV γ w hK b u)‖ :=
      congrArg (fun v : lp (fun n => n07aAngularBandSpace hV γ w hK b n) 2 => ‖v‖)
        (n07aAngularLambda_coordinates hV γ w hK b u)
    _ ≤ _ := norm_angularDerivative_le hu

end ContinuousFlexibility.Statements
