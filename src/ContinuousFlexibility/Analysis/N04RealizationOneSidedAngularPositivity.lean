import ContinuousFlexibility.Analysis.CanonicalWholePositiveTransport

/-!
# Angular positivity for the same selected positive transport

The retained low certificate controls the original endpoint fields.
Their existing finite representatives preserve those exact positive
jets. The original angular interpolation theorem therefore proves
positivity for the displayed width, with no new choice of controls.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements
open scoped ContDiff

theorem n04Realization_oneSidedTransport_angle_positive
    (n : ℕ) {F : Bool → PolarPoint → PolarPoint} {q : Bool → PolarPoint → ℝ}
    {a b : Bool → ℝ} {l r c d κ κX M H : ℝ}
    (hlc : l < c) (hcd : c < d) (hdr : d < r)
    (hκ : 0 < κ) (hκone : κ ≤ 1) (hM : 0 ≤ M)
    (hdata : ∀ side, OneSidedTransportEndpoint (F side) (q side)
      (a side) (b side) (if side then r else l))
    (hbound : WholePositiveEndpointJetBounds n F q l r κ κX M H)
    (t θ : ℝ) :
    0 < deriv (fun η => wholeComponentEndpointAngle n
      (oneSidedEndpointRepresentative (n + 2) l r (fun side p => (F side p).2))
      l r c d κ M (t, η)) θ := by
  let ψ : Bool → PolarPoint → ℝ := fun side p => (F side p).2
  let Ψ : Bool → PolarPoint → ℝ := oneSidedEndpointRepresentative (n + 2) l r ψ
  have hroot (side : Bool) (η : ℝ) :
      ContDiffAt ℝ ∞ (ψ side) (if side then r else l, η) :=
    ((hdata side).root_smooth η).snd
  have hΨ (side : Bool) : ContDiff ℝ ∞ (Ψ side) :=
    contDiff_oneSidedBoundaryTaylorRepresentative
      (if side then r else l) (hroot side) (n + 2)
  have heq (side : Bool) (k : ℕ) (hk : k ≤ n + 2) (η : ℝ) :
      iteratedFDeriv ℝ k (Ψ side) (if side then r else l, η) =
        iteratedFDeriv ℝ k (ψ side) (if side then r else l, η) :=
    iteratedFDeriv_oneSidedBoundaryTaylorRepresentative
      (hdata side).interval (hdata side).smooth_on.snd
      (hdata side).endpoint (hroot side) (n + 2) hk η
  have hangle (side : Bool) (η : ℝ) :
      κ ≤ angularPartial (Ψ side) (if side then r else l, η) := by
    have he := congrArg
      (fun A : PolarPoint [×1]→L[ℝ] ℝ => A (fun _ => (0, 1)))
      (heq side 1 (by omega) η)
    have he' : angularPartial (Ψ side) (if side then r else l, η) =
        angularPartial (ψ side) (if side then r else l, η) := by
      simpa only [iteratedFDeriv_one_apply, angularPartial] using he
    rw [he']
    exact hbound.angular_lower side η
  have hjets (side : Bool) (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 2) (η : ℝ) :
      ‖iteratedFDeriv ℝ k (Ψ side) (if side then r else l, η)‖ ≤ M := by
    rw [heq side k hkn η]
    calc
      ‖iteratedFDeriv ℝ k (ψ side) (if side then r else l, η)‖ ≤
          ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ *
            ‖iteratedFDeriv ℝ k (F side) (if side then r else l, η)‖ := by
        simpa only [ψ, ContinuousLinearMap.coe_snd', Function.comp_def] using
          (ContinuousLinearMap.snd ℝ ℝ ℝ).norm_iteratedFDeriv_comp_left
            ((hdata side).root_smooth η) (by simp : (k : ℕ∞ω) ≤ ∞)
      _ ≤ ‖iteratedFDeriv ℝ k (F side) (if side then r else l, η)‖ :=
        mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ)
      _ ≤ M := hbound.coordinate_jets side k hk hkn η
  have hlift (side : Bool) (x η : ℝ) :
      Ψ side (x, η + Real.pi) = Ψ side (x, η) + Real.pi := by
    apply oneSidedBoundaryTaylorRepresentative_lift
      (hdata side).interval (hdata side).endpoint (hroot side)
    intro s hs α
    simpa only [ψ, Prod.mk_add_mk, Prod.snd_add, add_zero] using
      congrArg Prod.snd ((hdata side).period_add (s, α) ⟨hs, mem_univ _⟩)
  have hodd (side : Bool) (x η : ℝ) :
      Ψ side (x, -η) = -Ψ side (x, η) := by
    apply oneSidedBoundaryTaylorRepresentative_odd
      (hdata side).interval (hdata side).endpoint (hroot side)
    intro s hs α
    exact congrArg Prod.snd ((hdata side).reflect (s, α) ⟨hs, mem_univ _⟩)
  have hang := rawEndpointAngularInterpolation_family (ι := Unit) (n + 1)
    (ψ := fun _ => Ψ) hlc hcd hdr hκ hκone hM
    (fun _ side => hΨ side) (fun _ side => hangle side)
    (fun _ side => hjets side) (fun _ side => hlift side) (fun _ side => hodd side)
  exact (half_pos hκ).trans_le ((hang.2.2.2.2.2 ()).2.1 t θ)

end ContinuousFlexibility.Analysis
