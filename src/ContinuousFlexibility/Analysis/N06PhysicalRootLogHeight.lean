import ContinuousFlexibility.Analysis.N06RootLogHeight
import ContinuousFlexibility.Analysis.N06FactoredRootJetSmallness
import ContinuousFlexibility.Analysis.N01RadialFlow
import ContinuousFlexibility.Analysis.SolveReturnEquations

/-!
# Cancellation of the actual height denominator in root heights

The original leading coefficient multiplied by the actual factored
characteristic speed is sqrt(reference radicand) divided by the actual
discriminant. In particular the height-Q denominator cancels exactly.
For the same physical reference factor, current and reference root
log-heights therefore differ by one half log(discriminant) and one sixth
of the difference of the logarithms of their actual odd fields. N01
supplies the local admissibility needed for every boundary jet.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements
open scoped ContDiff Topology

def n06RootPhysicalLeading (w : ℝ → ℝ) (u : PolarPoint → ℝ) (r ι : ℝ)
    (p : PolarPoint) : ℝ :=
  polarLinearA w u (rootProfileShift r ι p)

def n06RootPhysicalDiscriminant (w : ℝ → ℝ) (u : PolarPoint → ℝ) (r ι : ℝ)
    (p : PolarPoint) : ℝ :=
  polarDiscriminant w u (rootProfileShift r ι p)

/-- This identity is for the actual physical formulas. It does not
assume an identity of their derivatives or a smallness estimate. -/
theorem n06_actual_leading_mul_factoredSpeed
    (wref g w : ℝ → ℝ) (u : PolarPoint → ℝ) (r ι : ℝ) (p : PolarPoint)
    (hD : 0 < polarDiscriminant w u (rootProfileShift r ι p))
    (hQ : heightQ (profileEnergy w (rootProfileShift r ι p))
      (heightRadial u (rootProfileShift r ι p))
      (angularPartial (heightAngular u) (rootProfileShift r ι p)) ≠ 0) :
    n06RootPhysicalLeading w u r ι p * factoredCharacteristicSpeed wref g w u r ι p =
      Real.sqrt (rootProfileRadicand wref g r ι p.1) /
        n06RootPhysicalDiscriminant w u r ι p := by
  dsimp only [n06RootPhysicalLeading, n06RootPhysicalDiscriminant,
    polarLinearA, linearRadial, polarScale, inverseDThreeHalves, factoredCharacteristicSpeed]
  field_simp [hQ, hD.ne', (Real.sqrt_pos.mpr hD).ne']
  <;> ring

/-- The same cancellation in the fixed reference-factor notation used
by the root coefficient estimates. -/
theorem n06_actual_leading_mul_factoredSpeed_reference
    (wref g w : ℝ → ℝ) (u : PolarPoint → ℝ) (r ι : ℝ) (p : PolarPoint)
    (hwref : wref (r + ι * p.1) ≠ 0)
    (hD : 0 < polarDiscriminant w u (rootProfileShift r ι p))
    (hQ : heightQ (profileEnergy w (rootProfileShift r ι p))
      (heightRadial u (rootProfileShift r ι p))
      (angularPartial (heightAngular u) (rootProfileShift r ι p)) ≠ 0) :
    n06RootPhysicalLeading w u r ι p * factoredCharacteristicSpeed wref g w u r ι p =
      (wref (r + ι * p.1) * referenceRootSpeedFactor wref g r ι p.1) /
        n06RootPhysicalDiscriminant w u r ι p := by
  have hk : wref (r + ι * p.1) * referenceRootSpeedFactor wref g r ι p.1 =
      Real.sqrt (rootProfileRadicand wref g r ι p.1) := by
    dsimp only [referenceRootSpeedFactor]
    field_simp [hwref]
  exact (n06_actual_leading_mul_factoredSpeed wref g w u r ι p hD hQ).trans
    (congrArg (fun x : ℝ => x / n06RootPhysicalDiscriminant w u r ι p) hk.symm)

namespace N04bRootCoordinateProperties

variable {d c d₀ c₀ : PolarPoint → ℝ} {β β₀ : ℝ → ℝ}
  {Φ Φ₀ : ℝ → ℝ → ℝ} {R R₀ σ σ₀ : ℝ}
  {G G₀ : ℝ × ℝ × ℝ → ℝ}

/-- The true positive-side identity for two actual root constructions
using the same reference radial factor. -/
theorem n06_actualLogHeight_difference
    (P : N04bRootCoordinateProperties d c β Φ R σ G)
    (P₀ : N04bRootCoordinateProperties d₀ c₀ β₀ Φ₀ R₀ σ₀ G₀)
    (wref g w w₀ : ℝ → ℝ) (u u₀ : PolarPoint → ℝ) (r ι : ℝ)
    {p : PolarPoint} (hp : 0 < p.1)
    (hO : 0 < extendedRootOddCoefficient G p)
    (hO₀ : 0 < extendedRootOddCoefficient G₀ p)
    (hRad : 0 < rootProfileRadicand wref g r ι p.1)
    (hD : 0 < n06RootPhysicalDiscriminant w u r ι p)
    (hD₀ : 0 < n06RootPhysicalDiscriminant w₀ u₀ r ι p)
    (hQ : heightQ (profileEnergy w (rootProfileShift r ι p))
      (heightRadial u (rootProfileShift r ι p))
      (angularPartial (heightAngular u) (rootProfileShift r ι p)) ≠ 0)
    (hQ₀ : heightQ (profileEnergy w₀ (rootProfileShift r ι p))
      (heightRadial u₀ (rootProfileShift r ι p))
      (angularPartial (heightAngular u₀) (rootProfileShift r ι p)) ≠ 0)
    (hc : c p = factoredCharacteristicSpeed wref g w u r ι p)
    (hc₀ : c₀ p = factoredCharacteristicSpeed wref g w₀ u₀ r ι p) :
    Real.log (rootSmoothHeight (n06RootPhysicalLeading w u r ι) G p) -
        Real.log (rootSmoothHeight (n06RootPhysicalLeading w₀ u₀ r ι) G₀ p) =
      (1 / 2 : ℝ) *
        (Real.log (n06RootPhysicalDiscriminant w u r ι p) -
          Real.log (n06RootPhysicalDiscriminant w₀ u₀ r ι p)) +
        (1 / 6 : ℝ) *
          (Real.log (extendedRootOddCoefficient G p) -
            Real.log (extendedRootOddCoefficient G₀ p)) := by
  have he : n06RootPhysicalLeading w u r ι p * c p =
      Real.sqrt (rootProfileRadicand wref g r ι p.1) /
        n06RootPhysicalDiscriminant w u r ι p := by
    rw [hc]
    exact n06_actual_leading_mul_factoredSpeed wref g w u r ι p hD hQ
  have he₀ : n06RootPhysicalLeading w₀ u₀ r ι p * c₀ p =
      Real.sqrt (rootProfileRadicand wref g r ι p.1) /
        n06RootPhysicalDiscriminant w₀ u₀ r ι p := by
    rw [hc₀]
    exact n06_actual_leading_mul_factoredSpeed wref g w₀ u₀ r ι p hD₀ hQ₀
  have hac : 0 < n06RootPhysicalLeading w u r ι p * c p := by
    rw [he]
    exact div_pos (Real.sqrt_pos.mpr hRad) hD
  have hac₀ : 0 < n06RootPhysicalLeading w₀ u₀ r ι p * c₀ p := by
    rw [he₀]
    exact div_pos (Real.sqrt_pos.mpr hRad) hD₀
  rw [P.n06_logHeight_eq_regular _ hp hO hac,
    P₀.n06_logHeight_eq_regular _ hp hO₀ hac₀, he, he₀,
    Real.log_div (Real.sqrt_pos.mpr hRad).ne' hD.ne',
    Real.log_div (Real.sqrt_pos.mpr hRad).ne' hD₀.ne',
    Real.log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0) hO.ne',
    Real.log_mul (by norm_num : (3 / 2 : ℝ) ≠ 0) hO₀.ne']
  ring

end N04bRootCoordinateProperties

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

private theorem n06_rootLog_N01_denominators
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p ∧
      0 < heightQ (profileEnergy (stateProfile D S C z.1) p)
        (heightRadial (stateHeight D S C z) p)
        (angularPartial (heightAngular (stateHeight D S C z)) p) := by
  have h := hN.2.2.2.2.2.2.2.2.2.1 z hz hs p hp
  have hw : 0 < D.w p.1 := hN.1.1.choose_spec.1.2.2.2.2.1 p.1 hp.1
  have hws : 0 < stateProfile D S C z.1 p.1 :=
    (div_pos_iff_of_pos_right hw).mp (lt_of_lt_of_le (by norm_num) h.1)
  exact ⟨lt_of_lt_of_le (by norm_num) h.2.2.2.2.1,
    (div_pos_iff_of_pos_right hws).mp (lt_of_lt_of_le (by norm_num) h.2.2.1)⟩

private theorem n06_rootLog_N01_regular
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) {p : PolarPoint} (hp : p ∈ annularOpen D) :
    ContDiffAt ℝ ∞ (polarLinearA (stateProfile D S C z.1) (stateHeight D S C z)) p ∧
      0 < polarLinearA (stateProfile D S C z.1) (stateHeight D S C z) p ∧
      ContDiffAt ℝ ∞ (polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z)) p ∧
      0 < polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) p := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN z.1
  have hu := neighborhood_stateHeight_contDiff hT hS hw
  obtain ⟨hdisc, hQ⟩ := n06_rootLog_N01_denominators hN hz hs hp
  have hr : p.1 ≠ 0 := (hN.1.1.choose_spec.1.1.trans hp.1.1).ne'
  have hA := (contDiffAt_heightLinearCoefficients hw.contDiffAt hu.contDiffAt hr hdisc hQ.ne').1
  have hE : ContDiffAt ℝ ∞ (profileEnergy (stateProfile D S C z.1)) p :=
    contDiffAt_const.add ((hw.contDiffAt.comp p contDiffAt_fst).pow 2)
  have hk := contDiffAt_heightRadial hu.contDiffAt (m := ∞) (by simp)
  have ht := contDiffAt_heightAngular hu.contDiffAt (m := ∞) (by simp) hr
  have hDisc : ContDiffAt ℝ ∞
      (polarDiscriminant (stateProfile D S C z.1) (stateHeight D S C z)) p :=
    (hE.mul (contDiffAt_const.sub (ht.pow 2))).sub (hk.pow 2)
  exact ⟨hA, mul_pos hQ (inverseDThreeHalves_pos _ hdisc), hDisc, hdisc⟩

private theorem n06_rootLog_center_bound
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Seminorm ℝ E) (x : E) {ε : ℝ} (hε : 0 < ε) : p (x - x) < ε := by
  simpa only [sub_self, map_zero] using hε

theorem n06_root_discriminant_zero_parameter
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε) (x : AnnularState S) (p : PolarPoint) :
    polarDiscriminant (stateProfile D S C x) (stateHeight D S C (x, 0)) p = 1 := by
  have hw := contDiff_stateProfile_of_n01 hS hT hN x
  rw [stateHeight_zero_radial]
  exact Radial.polarDiscriminant_radialHeightField
    (stateRadialHeight_hasDerivAt_of_contDiff hw) p

/-- These are the actual current and reference root heights, with only
their primitive speed-factor germs retained. All admissibility and
smoothness of the physical coefficients are consequences of the original
N01 hypotheses. The equality supplies every boundary order, including
the exact three jets needed by the logarithmic-height patch. -/
theorem n06_N01_rootLogHeight_difference_boundaryJets
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1)
    {d c d₀ c₀ : PolarPoint → ℝ} {β β₀ : ℝ → ℝ}
    {Φ Φ₀ : ℝ → ℝ → ℝ} {R R₀ σ σ₀ : ℝ}
    {G G₀ : ℝ × ℝ × ℝ → ℝ}
    (P : N04bRootCoordinateProperties d c β Φ R σ G)
    (P₀ : N04bRootCoordinateProperties d₀ c₀ β₀ Φ₀ R₀ σ₀ G₀)
    {r : ℝ} (hr : r ∈ radialCore D) (ι θ : ℝ)
    {g : ℝ → ℝ} (hg : ContinuousAt g 0) (hg0 : 0 < g 0)
    (hc : c =ᶠ[𝓝 ((0, θ) : PolarPoint)]
      factoredCharacteristicSpeed D.w g (stateProfile D S C z.1) (stateHeight D S C z) r ι)
    (hc₀ : c₀ =ᶠ[𝓝 ((0, θ) : PolarPoint)]
      factoredCharacteristicSpeed D.w g (stateProfile D S C C.referenceState)
        (stateHeight D S C (C.referenceState, 0)) r ι)
    (n : ℕ) :
    radialBoundaryJet (fun p =>
      Real.log (rootSmoothHeight
        (n06RootPhysicalLeading (stateProfile D S C z.1) (stateHeight D S C z) r ι) G p) -
      Real.log (rootSmoothHeight
        (n06RootPhysicalLeading (stateProfile D S C C.referenceState)
          (stateHeight D S C (C.referenceState, 0)) r ι) G₀ p)) 0 n θ =
    radialBoundaryJet (fun p =>
      (1 / 2 : ℝ) * Real.log
        (n06RootPhysicalDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) r ι p) +
      (1 / 6 : ℝ) * (Real.log (extendedRootOddCoefficient G p) -
        Real.log (extendedRootOddCoefficient G₀ p))) 0 n θ := by
  have hz₀ : (C.referenceState, 0) ∈ stateNeighborhood S C base ε :=
    ⟨n06_rootLog_center_bound (stateGrading S base) C.referenceState hN.2.1,
      by simpa only [abs_zero] using hN.2.1⟩
  have hs₀ : stateSector S C.referenceState := hN.2.2.1.stateSector
  have hp₀ : (r, θ) ∈ annularOpen D := ⟨hr, mem_univ θ⟩
  have hreg := n06_rootLog_N01_regular hT hS hN hz hs hp₀
  have hreg₀ := n06_rootLog_N01_regular hT hS hN hz₀ hs₀ hp₀
  let a := n06RootPhysicalLeading (stateProfile D S C z.1) (stateHeight D S C z) r ι
  let a₀ := n06RootPhysicalLeading (stateProfile D S C C.referenceState)
    (stateHeight D S C (C.referenceState, 0)) r ι
  let disc := n06RootPhysicalDiscriminant (stateProfile D S C z.1) (stateHeight D S C z) r ι
  have ha : ContDiffAt ℝ ∞ a (0, θ) := by
    have hsource := hreg.1
    rw [← n06_rootProfileShift_boundary r ι θ] at hsource
    exact hsource.comp (0, θ) (n06_rootProfileShift_contDiff r ι).contDiffAt
  have ha₀ : ContDiffAt ℝ ∞ a₀ (0, θ) := by
    have hsource := hreg₀.1
    rw [← n06_rootProfileShift_boundary r ι θ] at hsource
    exact hsource.comp (0, θ) (n06_rootProfileShift_contDiff r ι).contDiffAt
  have hdisc : ContDiffAt ℝ ∞ disc (0, θ) := by
    have hsource := hreg.2.2.1
    rw [← n06_rootProfileShift_boundary r ι θ] at hsource
    exact hsource.comp (0, θ) (n06_rootProfileShift_contDiff r ι).contDiffAt
  have haPos : 0 < a (0, θ) := by
    simpa only [a, n06RootPhysicalLeading, n06_rootProfileShift_boundary] using hreg.2.1
  have ha₀Pos : 0 < a₀ (0, θ) := by
    simpa only [a₀, n06RootPhysicalLeading, n06_rootProfileShift_boundary] using hreg₀.2.1
  have hdiscPos : 0 < disc (0, θ) := by
    simpa only [disc, n06RootPhysicalDiscriminant, n06_rootProfileShift_boundary] using hreg.2.2.2
  have hh := P.height_boundary θ ha haPos
  have hh₀ := P₀.height_boundary θ ha₀ ha₀Pos
  have hO : 0 < extendedRootOddCoefficient G (0, θ) := by
    simpa only [extendedRootOddCoefficient_of_nonneg G (le_refl (0 : ℝ))] using P.odd_positive θ
  have hO₀ : 0 < extendedRootOddCoefficient G₀ (0, θ) := by
    simpa only [extendedRootOddCoefficient_of_nonneg G₀ (le_refl (0 : ℝ))] using P₀.odd_positive θ
  have hleft : ContDiffAt ℝ ∞ (fun p =>
      Real.log (rootSmoothHeight a G p) - Real.log (rootSmoothHeight a₀ G₀ p)) (0, θ) :=
    (hh.2.1.log hh.2.2.1.ne').sub (hh₀.2.1.log hh₀.2.2.1.ne')
  have hright : ContDiffAt ℝ ∞ (fun p =>
      (1 / 2 : ℝ) * Real.log (disc p) + (1 / 6 : ℝ) *
        (Real.log (extendedRootOddCoefficient G p) -
          Real.log (extendedRootOddCoefficient G₀ p))) (0, θ) :=
    (contDiffAt_const.mul (hdisc.log hdiscPos.ne')).add
      (contDiffAt_const.mul ((P.n06_extendedOdd_smooth.contDiffAt.log hO.ne').sub
        (P₀.n06_extendedOdd_smooth.contDiffAt.log hO₀.ne')))
  have hline : ContDiffAt ℝ ∞ (fun x : ℝ => (x, θ)) 0 :=
    contDiffAt_id.prodMk contDiffAt_const
  have hnear : ∀ᶠ x : ℝ in 𝓝 0,
      rootProfileShift r ι (x, θ) ∈ annularOpen D := by
    have hbase : rootProfileShift r ι (0, θ) ∈ annularOpen D := by
      simpa only [n06_rootProfileShift_boundary] using hp₀
    exact (((n06_rootProfileShift_contDiff r ι).contDiffAt.comp 0 hline).continuousAt.tendsto).eventually
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hbase)
  have hgp : ∀ᶠ x : ℝ in 𝓝 0, 0 < g x := hg.tendsto.eventually (Ioi_mem_nhds hg0)
  have hOp : ∀ᶠ x : ℝ in 𝓝 0, 0 < extendedRootOddCoefficient G (x, θ) :=
    (P.n06_extendedOdd_smooth.contDiffAt.comp 0 hline).continuousAt.tendsto.eventually
      (Ioi_mem_nhds hO)
  have hO₀p : ∀ᶠ x : ℝ in 𝓝 0, 0 < extendedRootOddCoefficient G₀ (x, θ) :=
    (P₀.n06_extendedOdd_smooth.contDiffAt.comp 0 hline).continuousAt.tendsto.eventually
      (Ioi_mem_nhds hO₀)
  apply n06_iteratedDeriv_eq_of_positive_germ (hleft.comp 0 hline)
    (hright.comp 0 hline) (n := n)
  filter_upwards [hc.comp_tendsto hline.continuousAt.tendsto,
    hc₀.comp_tendsto hline.continuousAt.tendsto, hnear, hgp, hOp, hO₀p]
    with x hxc hxc₀ hxcore hxg hxO hxO₀ hx
  have hb := n06_rootLog_N01_denominators hN hz hs hxcore
  have hb₀ := n06_rootLog_N01_denominators hN hz₀ hs₀ hxcore
  have hRad : 0 < rootProfileRadicand D.w g r ι x :=
    rootProfileRadicand_pos (hN.1.1.choose_spec.1.1.trans hxcore.1.1)
      (hN.1.1.choose_spec.1.2.2.2.2.1 _ hxcore.1) hxg
  have he := P.n06_actualLogHeight_difference P₀ D.w g
    (stateProfile D S C z.1) (stateProfile D S C C.referenceState)
    (stateHeight D S C z) (stateHeight D S C (C.referenceState, 0)) r ι
    (p := (x, θ)) hx hxO hxO₀ hRad hb.1 hb₀.1 hb.2.ne' hb₀.2.ne' hxc hxc₀
  have hzero : n06RootPhysicalDiscriminant (stateProfile D S C C.referenceState)
      (stateHeight D S C (C.referenceState, 0)) r ι (x, θ) = 1 :=
    n06_root_discriminant_zero_parameter hT hS hN C.referenceState _
  simpa only [hzero, Real.log_one, sub_zero] using he

end ContinuousFlexibility.Statements
