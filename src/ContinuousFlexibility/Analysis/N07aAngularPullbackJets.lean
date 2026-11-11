import ContinuousFlexibility.Analysis.N07aAngularPhysicalCoefficients
import ContinuousFlexibility.Analysis.N07aCanonicalGreenPairing

/-!
# Angular L² jets of the actual chart pullback

The first chain rule has two bounded geometric coefficients. Induction
simultaneously over all canonical mixed derivatives gives every physical
angular derivative in L². Thus no periodic radial extension or regularity
certificate for the pulled-back unknown is needed.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter MeasureTheory
open ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

variable {S : PhysicalSpacesData} {K P : CanonicalData S} {m : ℕ}

theorem N07aCanonicalOpenCoefficient.memLp_mul
    (χ : N07aCanonicalOpenCoefficient S P m) {f : PolarPoint → ℝ}
    (hf : MemLp f 2 (canonicalMeasure S P m)) :
    MemLp (fun p => χ.value p * f p) 2 (canonicalMeasure S P m) := by
  apply hf.of_le_mul (c := χ.bound)
    ((n07a_canonicalOpen_aestronglyMeasurable χ.smooth.continuousOn).mul
      hf.aestronglyMeasurable)
  filter_upwards [χ.bound_ae] with p hp
  simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)

/-- Finite Leibniz expansion uses only the already known lower angular jets. -/
theorem n07a_angularJet_memLp_mul
    (χ : N07aCanonicalOpenCoefficient S P m) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S P m)) (n : ℕ)
    (hLp : ∀ j ≤ n, MemLp (mixedDerivative 0 j f) 2 (canonicalMeasure S P m)) :
    MemLp (mixedDerivative 0 n (fun p => χ.value p * f p)) 2
      (canonicalMeasure S P m) := by
  have hsum : MemLp (fun p => ∑ j ∈ Finset.range (n + 1),
      (n.choose j : ℝ) * (mixedDerivative 0 j χ.value p *
        mixedDerivative 0 (n - j) f p)) 2 (canonicalMeasure S P m) := by
    apply memLp_finsetSum
    intro j hj
    exact ((χ.jet 0 j).memLp_mul (hLp (n - j) (Nat.sub_le _ _))).const_mul _
  apply (memLp_congr_ae (show mixedDerivative 0 n (fun p => χ.value p * f p) =ᵐ[
      canonicalMeasure S P m] (fun p => ∑ j ∈ Finset.range (n + 1),
        (n.choose j : ℝ) * (mixedDerivative 0 j χ.value p *
          mixedDerivative 0 (n - j) f p)) from ?_)).mpr hsum
  filter_upwards [n07a_canonicalOpen_ae (S := S) (K := P) (m := m)] with p hp
  rw [n07a_mixedDerivative_mul_on (isOpen_Ioo.prod isOpen_univ) χ.smooth hf 0 n hp]
  simp only [Nat.zero_add, Finset.sum_range_one, Nat.choose_zero_right,
    Nat.cast_one, one_mul, Nat.sub_zero, mul_assoc]

/-- The actual angular chain rule, with the two true chart component derivatives. -/
theorem n07a_angular_comp_chain {Φ : PolarPoint → PolarPoint} {f : PolarPoint → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ (canonicalOpen S P m))
    (hmap : MapsTo Φ (canonicalOpen S P m) (canonicalOpen S K m))
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m)) :
    EqOn (mixedDerivative 0 1 (f ∘ Φ))
      (fun p => mixedDerivative 0 1 (fun q => (Φ q).1) p * mixedDerivative 1 0 f (Φ p) +
        mixedDerivative 0 1 (fun q => (Φ q).2) p * mixedDerivative 0 1 f (Φ p))
      (canonicalOpen S P m) := by
  intro p hp
  have hU : IsOpen (canonicalOpen S P m) := isOpen_Ioo.prod isOpen_univ
  have hV : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have hΦd := (hΦ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hfd := (hf.contDiffAt (hV.mem_nhds (hmap hp))).differentiableAt (by simp)
  have hR : (fderiv ℝ Φ p (0, 1)).1 =
      mixedDerivative 0 1 (fun q => (Φ q).1) p := by
    rw [← n07a_open_angularPartial_eq hΦ.fst hp, angularPartial, fderiv.fst hΦd,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst']
  have hA : (fderiv ℝ Φ p (0, 1)).2 =
      mixedDerivative 0 1 (fun q => (Φ q).2) p := by
    rw [← n07a_open_angularPartial_eq hΦ.snd hp, angularPartial, fderiv.snd hΦd,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd']
  have hv : fderiv ℝ Φ p (0, 1) =
      (fderiv ℝ Φ p (0, 1)).1 • (1, 0) +
        (fderiv ℝ Φ p (0, 1)).2 • (0, 1) := by
    ext <;> simp
  calc
    _ = fderiv ℝ f (Φ p) (fderiv ℝ Φ p (0, 1)) := by
      rw [← n07a_open_angularPartial_eq (hf.comp hΦ hmap) hp, angularPartial,
        fderiv_comp _ hfd hΦd, ContinuousLinearMap.comp_apply]
    _ = (fderiv ℝ Φ p (0, 1)).1 * radialPartial f (Φ p) +
        (fderiv ℝ Φ p (0, 1)).2 * angularPartial f (Φ p) := by
      conv_lhs => rw [hv]
      rw [map_add, map_smul, map_smul]
      simp only [smul_eq_mul, radialPartial, angularPartial]
    _ = _ := by rw [hR, hA, n07a_open_radialPartial_eq hf (hmap hp),
      n07a_open_angularPartial_eq hf (hmap hp)]

/-- All actual mixed canonical jets are pulled back together. The angular
induction therefore never presupposes any high physical jet of the unknown. -/
theorem n07a_angular_pullback_mixed_memLp
    {Φ : PolarPoint → PolarPoint} {f : PolarPoint → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ (canonicalOpen S P m))
    (hmap : MapsTo Φ (canonicalOpen S P m) (canonicalOpen S K m))
    (χR χA : N07aCanonicalOpenCoefficient S P m)
    (hR : EqOn χR.value (mixedDerivative 0 1 (fun p => (Φ p).1)) (canonicalOpen S P m))
    (hA : EqOn χA.value (mixedDerivative 0 1 (fun p => (Φ p).2)) (canonicalOpen S P m))
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m))
    (hLp : ∀ a b, MemLp ((mixedDerivative a b f) ∘ Φ) 2 (canonicalMeasure S P m)) :
    ∀ n a b, MemLp (mixedDerivative 0 n ((mixedDerivative a b f) ∘ Φ)) 2
      (canonicalMeasure S P m) := by
  have hU : IsOpen (canonicalOpen S P m) := isOpen_Ioo.prod isOpen_univ
  have hV : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have hs (a b : ℕ) : ContDiffOn ℝ ∞ ((mixedDerivative a b f) ∘ Φ)
      (canonicalOpen S P m) :=
    (contDiffOn_mixedDerivative hV hf a b).comp hΦ hmap
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b
    cases n with
    | zero => simpa only [spaces_mixedDerivative_zero] using hLp a b
    | succ n =>
      have hfirst : EqOn (mixedDerivative 0 1 ((mixedDerivative a b f) ∘ Φ))
          (fun p => χR.value p * mixedDerivative (a + 1) b f (Φ p) +
            χA.value p * mixedDerivative a (b + 1) f (Φ p))
          (canonicalOpen S P m) := by
        intro p hp
        rw [n07a_angular_comp_chain hΦ hmap (contDiffOn_mixedDerivative hV hf a b) hp]
        dsimp only
        rw [← hR hp, ← hA hp,
          n07a_mixedDerivative_mixedDerivative_on hV hf 1 0 a b (hmap hp),
          n07a_mixedDerivative_mixedDerivative_on hV hf 0 1 a b (hmap hp)]
        simp only [zero_add, Nat.add_comm]
      have hLpR := n07a_angularJet_memLp_mul χR (hs (a + 1) b) n
        (fun j hj => ih j (by omega) (a + 1) b)
      have hLpA := n07a_angularJet_memLp_mul χA (hs a (b + 1)) n
        (fun j hj => ih j (by omega) a (b + 1))
      have he : mixedDerivative 0 (n + 1) ((mixedDerivative a b f) ∘ Φ) =ᵐ[
          canonicalMeasure S P m]
          (fun p => mixedDerivative 0 n (fun q => χR.value q *
              mixedDerivative (a + 1) b f (Φ q)) p +
            mixedDerivative 0 n (fun q => χA.value q *
              mixedDerivative a (b + 1) f (Φ q)) p) := by
        filter_upwards [n07a_canonicalOpen_ae (S := S) (K := P) (m := m)] with p hp
        have hd := n07a_mixedDerivative_eqOn hU hfirst 0 n hp
        rw [n07a_mixedDerivative_mixedDerivative_on hU (hs a b) 0 n 0 1 hp] at hd
        have hadd := n07a_mixedDerivative_add_on hU (χR.smooth.mul (hs (a + 1) b))
          (χA.smooth.mul (hs a (b + 1))) 0 n hp
        simp only [Function.comp_apply] at hadd
        rw [hadd] at hd
        simpa only [Nat.zero_add] using hd
      exact (memLp_congr_ae he).mpr (hLpR.add hLpA)

variable {D : ReferenceData} {T : MaterialData} {C : NonlinearGeometryData S}
  {L : ReturnCorrectionData S} {base loss : ℕ} {ε : ℝ}

/-- Every angular jet of the true current pullback is L², on the actual
physical interval and using the given primitive geometric bounds. -/
theorem n07a_current_chart_angular_memLp
    (h04 : N04Properties D T S C L K base loss ε)
    (href : CanonicalGeometry.ReferenceJets D T S C L K)
    (hcur : CanonicalGeometry.CurrentJets D T S C L K base ε)
    (z : CanonicalGeometry.Parameter S) (hz : z ∈ sectorNeighborhood S base ε ε)
    (hz' : liftSectorParameter S C z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S (liftSectorParameter S C z).1)
    (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (canonicalOpen S K m))
    (hLp : ∀ a b, MemLp (mixedDerivative a b f) 2 (canonicalMeasure S K m)) (n : ℕ) :
    MemLp (mixedDerivative 0 n (fun p => f (K.chart (liftSectorParameter S C z) m p))) 2
      (canonicalMeasure S (n07aPhysicalIntervalData K) m) := by
  have hm := (h04.2.2.2.1 m).1
  have hcan := (h04.2.2.2.1 m).2.1
  obtain ⟨hmap, _, _, _, hΦ, _⟩ := h04.2.2.2.2.2.2.2.1 _ hz' hs m
  have h := n07a_angular_pullback_mixed_memLp
    (P := n07aPhysicalIntervalData K) (K := K) (m := m) hΦ hmap
    (n07aChartRadialAngularCoefficient href hcur z hz m hm)
    (n07aChartAngularAngularCoefficient href hcur z hz m hm)
    (fun p _ => congrFun (n07aChartRadialAngularCoefficient_value href hcur z hz m hm hcan) p)
    (n07aChartAngularAngularCoefficient_value href hcur z hz m hm)
    hf (fun a b => n07a_current_chart_memLp_pullback h04 href hcur z hz hz' hs m (hLp a b))
    n 0 0
  simpa only [spaces_mixedDerivative_zero, Function.comp_def] using h

end ContinuousFlexibility.Analysis
