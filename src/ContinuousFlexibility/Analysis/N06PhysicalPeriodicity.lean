import ContinuousFlexibility.Analysis.N06PhysicalReconstruction

/-!
# Periodicity of the actual reconstructed source

The lift identity of a smooth chart implies periodicity of its actual
Fréchet derivative and Jacobian. Consequently the physical source weight
used in the canonical source formula is periodic as well as the height.
-/

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory
open scoped Topology ContDiff

set_option backward.isDefEq.respectTransparency false

/-- Differentiating an angular lift identity on an open strip preserves
the full derivative, including both coordinate directions. -/
theorem n06_fderiv_chart_lift {F : PolarPoint → PolarPoint} {l r τ : ℝ}
    (hF : ContDiffOn ℝ ∞ F (Ioo l r ×ˢ (univ : Set ℝ)))
    (hlift : ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ),
      F (p + (0, τ)) = F p + (0, τ))
    {p : PolarPoint} (hp : p ∈ Ioo l r ×ˢ (univ : Set ℝ)) :
    fderiv ℝ F (p + (0, τ)) = fderiv ℝ F p := by
  have hopen : IsOpen (Ioo l r ×ˢ (univ : Set ℝ)) := isOpen_Ioo.prod isOpen_univ
  have hp' : p + (0, τ) ∈ Ioo l r ×ˢ (univ : Set ℝ) := by
    exact ⟨by simpa only [Prod.fst_add, add_zero] using hp.1, mem_univ _⟩
  have hd : HasFDerivAt (fun q : PolarPoint => F (q + (0, τ)))
      (fderiv ℝ F (p + (0, τ))) p := by
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq] using
      ((hF.contDiffAt (hopen.mem_nhds hp')).differentiableAt (by simp)).hasFDerivAt.comp p
        ((hasFDerivAt_id p).add_const (0, τ))
  have heq : (fun q : PolarPoint => F (q + (0, τ))) =ᶠ[𝓝 p]
      (fun q => F q + (0, τ)) := by
    filter_upwards [hopen.mem_nhds hp] with q hq
    exact hlift q hq
  have hdF := ((hF.contDiffAt (hopen.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
  have hd₀ : HasFDerivAt (fun q : PolarPoint => F q + (0, τ))
      (fderiv ℝ F p) p := hdF.add_const (0, τ)
  exact hd.unique (hd₀.congr_of_eventuallyEq heq)

theorem n06_planeJacobian_chart_lift {F : PolarPoint → PolarPoint} {l r τ : ℝ}
    (hF : ContDiffOn ℝ ∞ F (Ioo l r ×ˢ (univ : Set ℝ)))
    (hlift : ∀ p ∈ Ioo l r ×ˢ (univ : Set ℝ),
      F (p + (0, τ)) = F p + (0, τ))
    {p : PolarPoint} (hp : p ∈ Ioo l r ×ˢ (univ : Set ℝ)) :
    planeJacobian F (p + (0, τ)) = planeJacobian F p := by
  unfold planeJacobian
  rw [n06_fderiv_chart_lift hF hlift hp]

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {L : ReturnCorrectionData S} {K : CanonicalData S}
  {base loss : ℕ} {ε : ℝ}

/-- The source multiplier is the Jacobian divided by the actual height;
its periodicity is a consequence of N04, not a separate assumption. -/
theorem n06_physicalSourceWeight_periodic
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (m : ℕ) {p : PolarPoint}
    (hp : p ∈ physicalPieceOpen S K m) :
    |planeJacobian (K.chart z m) (p + (0, Real.pi))| /
        K.height z m (p + (0, Real.pi)) =
      |planeJacobian (K.chart z m) p| / K.height z m p := by
  obtain ⟨_, _, _, _, _, _, _, hcharts, _⟩ := hN04
  obtain ⟨_, _, _, _, hchart, _, _, hlift⟩ := hcharts z hz hs m
  rw [n06_planeJacobian_chart_lift hchart (fun q hq => (hlift q hq).2.2.1) hp,
    (hlift p hp).2.2.2]

/-- Every reconstructed canonical source has a genuine half-periodic
physical representative, without regularity assumptions on the L² data. -/
theorem n06PhysicalSource_periodic
    (hN04 : N04Properties D T S C L K base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) (f : ℕ → PolarPoint → ℝ) :
    Function.Periodic
      (n06PhysicalReconstruct K z f
        (fun m p => |planeJacobian (K.chart z m) p| / K.height z m p))
      (0, Real.pi) :=
  n06PhysicalReconstruct_periodic hN04 hz hs f _
    (fun m _ hp => n06_physicalSourceWeight_periodic hN04 hz hs m hp)

end ContinuousFlexibility.Statements
