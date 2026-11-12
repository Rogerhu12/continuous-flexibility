import ContinuousFlexibility.Analysis.ReturnChartIdentities
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Positivity of the actual right-chart derivative

The positive derivative of the minus return makes it strictly increasing.
Its specified two-sided inverse is therefore monotone, surjective and
continuous.  The inverse derivative theorem then applies to that very
inverse.  The transported left chart has positive derivative, and taking
its odd part averages the derivatives at the two reflected points.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

set_option backward.isDefEq.respectTransparency false

/-- The derivative of an already specified inverse of an increasing map.
No differentiability or continuity of the inverse is assumed. -/
theorem returnChart_hasDerivAt_inverse (f g : ℝ → ℝ)
    (hfpos : ∀ θ, 0 < deriv f θ)
    (hleft : ∀ θ, g (f θ) = θ) (hright : ∀ θ, f (g θ) = θ)
    (θ : ℝ) : HasDerivAt g (deriv f (g θ))⁻¹ θ := by
  have hfmono : StrictMono f := strictMono_of_deriv_pos hfpos
  have hgmono : Monotone g := by
    intro a b hab
    apply hfmono.le_iff_le.mp
    simpa only [hright] using hab
  have hgsurj : Function.Surjective g := fun a => ⟨f a, hleft a⟩
  have hgc : Continuous g := hgmono.continuous_of_surjective hgsurj
  have hf : HasDerivAt f (deriv f (g θ)) (g θ) :=
    (differentiableAt_of_deriv_ne_zero (hfpos (g θ)).ne').hasDerivAt
  exact HasDerivAt.of_local_left_inverse hgc.continuousAt hf (hfpos (g θ)).ne'
    (Filter.Eventually.of_forall hright)

theorem returnChart_inverse_deriv_pos (f g : ℝ → ℝ)
    (hfpos : ∀ θ, 0 < deriv f θ)
    (hleft : ∀ θ, g (f θ) = θ) (hright : ∀ θ, f (g θ) = θ)
    (θ : ℝ) : 0 < deriv g θ := by
  rw [(returnChart_hasDerivAt_inverse f g hfpos hleft hright θ).deriv]
  exact inv_pos.mpr (hfpos (g θ))

theorem oddPart_hasDerivAt {f : ℝ → ℝ} {θ dpos dneg : ℝ}
    (hpos : HasDerivAt f dpos θ) (hneg : HasDerivAt f dneg (-θ)) :
    HasDerivAt (oddPart f) ((dpos + dneg) / 2) θ := by
  have hreflect : HasDerivAt (fun t => f (-t)) (-dneg) θ := by
    simpa only [mul_neg_one, Function.comp_def] using hneg.comp θ (hasDerivAt_neg (x := θ))
  have h := ((hpos.sub hreflect).div_const 2).congr_deriv
    (g' := (dpos + dneg) / 2) (by ring)
  exact h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => by simp only [oddPart, Pi.sub_apply])

theorem deriv_oddPart_pos (f : ℝ → ℝ) (hfpos : ∀ θ, 0 < deriv f θ) (θ : ℝ) :
    0 < deriv (oddPart f) θ := by
  have h := oddPart_hasDerivAt
    (differentiableAt_of_deriv_ne_zero (hfpos θ).ne').hasDerivAt
    (differentiableAt_of_deriv_ne_zero (hfpos (-θ)).ne').hasDerivAt
  rw [h.deriv]
  exact div_pos (add_pos (hfpos θ) (hfpos (-θ))) (by norm_num)

variable (S : PhysicalSpacesData) (C : NonlinearGeometryData S)
  (z : AnnularState S × ℝ) (m : ℕ)

/-- Positivity of the right chart follows from the two positively oriented
maps used to transport the left chart, followed by the odd projection. -/
theorem rightChartCandidate_deriv_pos
    (hleftPos : ∀ θ, 0 < deriv (stateLeftChart S z.1 m) θ)
    (hflowPos : ∀ θ, 0 < deriv (C.minusFlow z m (C.right m)) θ)
    (hreturnLeft : ∀ θ, C.minusReturnInverse z m (C.minusFlow z m (C.right m) θ) = θ)
    (hreturnRight : ∀ θ, C.minusFlow z m (C.right m) (C.minusReturnInverse z m θ) = θ)
    (θ : ℝ) : 0 < deriv (rightChartCandidate S C z m) θ := by
  apply deriv_oddPart_pos
  intro t
  have hinv := returnChart_hasDerivAt_inverse _ _ hflowPos hreturnLeft hreturnRight t
  have hleft := (differentiableAt_of_deriv_ne_zero
    (hleftPos (C.minusReturnInverse z m t)).ne').hasDerivAt
  have h : HasDerivAt
      (fun u => stateLeftChart S z.1 m (C.minusReturnInverse z m u) - C.travel m)
      (deriv (stateLeftChart S z.1 m) (C.minusReturnInverse z m t) *
        (deriv (C.minusFlow z m (C.right m)) (C.minusReturnInverse z m t))⁻¹) t := by
    simpa only [Function.comp_def] using (hleft.comp t hinv).sub_const (C.travel m)
  rw [h.deriv]
  exact mul_pos (hleftPos _) (inv_pos.mpr (hflowPos _))

theorem N01Properties.rightChart_deriv_pos {D : ReferenceData} {T : MaterialData}
    {base loss : ℕ} {ε : ℝ} (hN01 : N01Properties D T S C base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (θ : ℝ) : 0 < deriv (rightChartCandidate S C z m) θ := by
  rcases hN01 with ⟨_, _, _, hcontrol, _, _, hflow, hleft, hInv, _⟩
  have hI := hInv z hz hsector m
  apply rightChartCandidate_deriv_pos S C z m
  · intro t
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (hleft z hz hsector m t).1
  · intro t
    exact ((hflow z hz m t).2.2.2 (C.right m)
      ⟨(hcontrol.1 m).2.1.le, le_rfl⟩).1
  · intro t
    exact (hI t).2.1
  · intro t
    exact (hI t).1

/-- The entire first clause of N02 is already a consequence of N01;
the last inequality is the new inverse-calculus bridge proved above. -/
theorem N01Properties.return_inverse_and_positive {D : ReferenceData} {T : MaterialData}
    {base loss : ℕ} {ε : ℝ} (hN01 : N01Properties D T S C base loss ε)
    (hz : z ∈ stateNeighborhood S C base ε) (hsector : stateSector S z.1)
    (θ : ℝ) :
    C.minusFlow z m (C.right m) (C.minusReturnInverse z m θ) = θ ∧
    C.minusReturnInverse z m (C.minusFlow z m (C.right m) θ) = θ ∧
    rightChartCandidate S C z m (C.rightChartInverse z m θ) = θ ∧
    C.rightChartInverse z m (rightChartCandidate S C z m θ) = θ ∧
    0 < deriv (rightChartCandidate S C z m) θ := by
  have hpos := N01Properties.rightChart_deriv_pos S C z m hN01 hz hsector θ
  rcases hN01 with ⟨_, _, _, _, _, _, _, _, hInv, _⟩
  have hI := hInv z hz hsector m θ
  exact ⟨hI.1, hI.2.1, hI.2.2.1, hI.2.2.2, hpos⟩

end ContinuousFlexibility.Statements
