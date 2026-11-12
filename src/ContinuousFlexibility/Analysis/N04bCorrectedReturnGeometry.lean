import ContinuousFlexibility.Analysis.N01ReturnChartSmoothness
import ContinuousFlexibility.Analysis.ReturnCorrectionResidualPeriodicity

/-!
# The actual corrected return map is a smooth increasing circle lift

The exact N03 return identity identifies the corrected endpoint with
the actual N01 right-chart inverse composed with the shifted left chart.
Its smoothness, positive derivative and true inverse are consequences.
No regularity of the corrected endpoint map is assumed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set
open ContinuousFlexibility.Statements
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false

/-- The exact return equation determines the actual corrected endpoint
as a composition of two already constructed angular charts. -/
theorem n04b_corrected_return_eq
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) (θ : ℝ) :
    L.minusFlow z m (C.right m) θ =
      C.rightChartInverse z m (stateLeftChart S z.1 m θ - C.travel m) := by
  have hI := N01Properties.return_inverse_and_positive S C z m h03.1.1 hz hs
  have hreturn := (h03.2.2.2.2.2.1 z hz hs m θ).2.2.2.1
  calc
    L.minusFlow z m (C.right m) θ =
        C.rightChartInverse z m
          (rightChartCandidate S C z m (L.minusFlow z m (C.right m) θ)) :=
      ((hI (L.minusFlow z m (C.right m) θ)).2.2.2.1).symm
    _ = _ := congrArg (C.rightChartInverse z m) hreturn

/-- Smooth increasing angular geometry of the actual corrected endpoint
and its actual chosen inverse, obtained from the exact return identity. -/
theorem n04b_corrected_return_geometry
    {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
    {C : NonlinearGeometryData S} {R : ReturnEquationData S}
    {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (h03 : NonlinearPropertiesThrough03 D T S C R L base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) :
    let f : ℝ → ℝ := L.minusFlow z m (C.right m)
    let g : ℝ → ℝ := Function.invFun f
    ContDiff ℝ ∞ f ∧ (∀ θ, 0 < deriv f θ) ∧
      (∀ θ, f (θ + Real.pi) = f θ + Real.pi) ∧ Function.Bijective f ∧
      ContDiff ℝ ∞ g ∧ (∀ θ, 0 < deriv g θ) ∧
      (∀ θ, f (g θ) = θ ∧ g (f θ) = θ) ∧
      (∀ θ, g (θ + Real.pi) = g θ + Real.pi) := by
  let f : ℝ → ℝ := L.minusFlow z m (C.right m)
  let h : ℝ → ℝ := stateLeftChart S z.1 m
  let H : ℝ → ℝ := rightChartCandidate S C z m
  let G : ℝ → ℝ := C.rightChartInverse z m
  have hN := h03.1.1
  have hI := N01Properties.return_inverse_and_positive S C z m hN hz hs
  have hleft := hN.2.2.2.2.2.2.2.1 z hz hs m
  have hh : ContDiff ℝ ∞ h := stateLeftChart_contDiff S z m (hS.2.1 (3 / 4 : ℝ))
  have hG : ContDiff ℝ ∞ G := hN.rightChartInverse_contDiff hS hT hz hs m
  have hHpos : ∀ θ, 0 < deriv H θ :=
    N01Properties.rightChart_deriv_pos S C z m hN hz hs
  have hGpos : ∀ θ, 0 < deriv G θ :=
    returnChart_inverse_deriv_pos H G hHpos
      (fun θ => (hI θ).2.2.2.1) (fun θ => (hI θ).2.2.1)
  have hformula : f = (fun θ => G (h θ - C.travel m)) :=
    funext (n04b_corrected_return_eq h03 hz hs m)
  have hf : ContDiff ℝ ∞ f := by
    rw [hformula]
    exact hG.comp (hh.sub contDiff_const)
  have hfpos : ∀ θ, 0 < deriv f θ := by
    intro θ
    have hder :
        HasDerivAt f (deriv G (h θ - C.travel m) * deriv h θ) θ := by
      rw [hformula]
      simpa only [Function.comp_def] using
        ((hG.differentiable (by simp) _).hasDerivAt).comp θ
          (((hh.differentiable (by simp) θ).hasDerivAt).sub_const (C.travel m))
    rw [hder.deriv]
    exact mul_pos (hGpos _) (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (hleft θ).1)
  have hfperiod : ∀ θ, f (θ + Real.pi) = f θ + Real.pi := by
    intro θ
    rw [hformula]
    change G (h (θ + Real.pi) - C.travel m) = G (h θ - C.travel m) + Real.pi
    have hperiod : h (θ + Real.pi) = h θ + Real.pi := (hleft θ).2.2.1
    rw [hperiod,
      show h θ + Real.pi - C.travel m = (h θ - C.travel m) + Real.pi by ring]
    exact hN.rightChartInverse_add_period hz hs m (h θ - C.travel m)
  have hbij : Function.Bijective f :=
    ⟨(strictMono_of_deriv_pos hfpos).injective,
      returnLift_surjective Real.pi_pos hf.continuous hfperiod⟩
  have hleftInverse : ∀ θ, Function.invFun f (f θ) = θ :=
    Function.leftInverse_invFun hbij.1
  have hrightInverse : ∀ θ, f (Function.invFun f θ) = θ :=
    Function.rightInverse_invFun hbij.2
  exact ⟨hf, hfpos, hfperiod, hbij,
    returnChart_inverse_contDiff f (Function.invFun f) hf hfpos hleftInverse hrightInverse,
    returnChart_inverse_deriv_pos f (Function.invFun f) hfpos hleftInverse hrightInverse,
    fun θ => ⟨hrightInverse θ, hleftInverse θ⟩,
    returnLift_invFun_add_period hbij.1 hbij.2 hfperiod⟩

end ContinuousFlexibility.Analysis
