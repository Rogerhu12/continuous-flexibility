module

public import ContinuousFlexibility.Analysis.MaterialCylinderPointwise
public import ContinuousFlexibility.Analysis.SpacesMollifierL1
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Reconstructing smooth cylinder functions from all weak jets

Compact-local integral convergence of every mixed derivative yields
uniform convergence of every mixed derivative. The four-term cylinder
Sobolev estimate supplies this passage without a subsequence or an
auxiliary regularity hypothesis on the weak representatives.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set Filter MeasureTheory ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

/-- One fixed compact cylinder containing every unit window with
radial base point in `[-R,R]`. -/
def spacesCompactCylinder (R : ℝ) : Set PolarPoint :=
  Icc (-R) (R + 1) ×ˢ Icc 0 Real.pi

theorem spaces_isCompact_compactCylinder (R : ℝ) : IsCompact (spacesCompactCylinder R) :=
  isCompact_Icc.prod isCompact_Icc

private theorem spaces_cylinderWindow_subset {R x : ℝ} (hx : |x| ≤ R) :
    cylinderWindow x ⊆ spacesCompactCylinder R := by
  intro p hp
  obtain ⟨hxl, hxr⟩ := abs_le.mp hx
  exact ⟨⟨hxl.trans hp.1.1.le, hp.1.2.trans (by linarith)⟩,
    ⟨hp.2.1.le, hp.2.2⟩⟩

private theorem spaces_windowIntegral_le_compactCylinder
    {g : PolarPoint → ℝ} (hg : Continuous g) {R x : ℝ} (hx : |x| ≤ R) :
    (∫ p in cylinderWindow x, |g p|) ≤ ∫ p in spacesCompactCylinder R, |g p| :=
  setIntegral_mono_set
    (hg.abs.continuousOn.integrableOn_compact (spaces_isCompact_compactCylinder R))
    (Eventually.of_forall (fun _ => abs_nonneg _))
    (Eventually.of_forall (fun _ hp => spaces_cylinderWindow_subset hx hp))

/-- The local pointwise estimate is uniform throughout a compact radial
range and throughout all angular periods. -/
theorem spaces_abs_le_compactCylinder_L1 {g : PolarPoint → ℝ}
    (hg : ContDiff ℝ ∞ g)
    (hp : ∀ x : ℝ, Function.Periodic (fun θ => g (x, θ)) Real.pi)
    {R x : ℝ} (hx : |x| ≤ R) (θ : ℝ) :
    |g (x, θ)| ≤
      (∫ p in spacesCompactCylinder R, |g p|) +
      (∫ p in spacesCompactCylinder R, |radialPartial g p|) +
      (∫ p in spacesCompactCylinder R, |angularPartial g p|) +
      ∫ p in spacesCompactCylinder R, |radialPartial (angularPartial g) p| := by
  obtain ⟨t, ht, he⟩ := (hp x).exists_mem_Ico₀ Real.pi_pos θ
  change g (x, θ) = g (x, t) at he
  rw [he]
  exact (abs_le_cylinderWindow_L1 hg x t ⟨ht.1, ht.2.le⟩).trans
    (add_le_add (add_le_add (add_le_add
      (spaces_windowIntegral_le_compactCylinder hg.continuous hx)
      (spaces_windowIntegral_le_compactCylinder (contDiff_cylinder_radialPartial hg).continuous hx))
      (spaces_windowIntegral_le_compactCylinder (contDiff_cylinder_angularPartial hg).continuous hx))
      (spaces_windowIntegral_le_compactCylinder
        (contDiff_cylinder_radialPartial (contDiff_cylinder_angularPartial hg)).continuous hx))

private theorem spaces_radialPartial_sub {f g : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    radialPartial (fun p => f p - g p) = fun p => radialPartial f p - radialPartial g p :=
  funext (fun p => radialPartial_sub (hf.differentiable (by simp) p) (hg.differentiable (by simp) p))

private theorem spaces_angularPartial_sub {f g : PolarPoint → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    angularPartial (fun p => f p - g p) = fun p => angularPartial f p - angularPartial g p :=
  funext (fun p => angularPartial_sub (hf.differentiable (by simp) p) (hg.differentiable (by simp) p))

/-- Integral approximation of every mixed jet makes every mixed jet
uniformly Cauchy on each compact set of the whole cylinder plane. -/
theorem spaces_uniformCauchy_mixedDerivative_of_local_L1
    (f : ℕ → PolarPoint → ℝ) (g : ℕ → ℕ → PolarPoint → ℝ)
    (hf : ∀ n, ContDiff ℝ ∞ (f n))
    (hp : ∀ n x, Function.Periodic (fun θ => f n (x, θ)) Real.pi)
    (hg : ∀ a b, LocallyIntegrable (g a b) volume)
    (hlim : ∀ a b K, IsCompact K → Tendsto
      (fun n => ∫ p in K, |mixedDerivative a b (f n) p - g a b p|) atTop (𝓝 0))
    (a b : ℕ) {K : Set PolarPoint} (hK : IsCompact K) :
    UniformCauchySeqOn (fun n => mixedDerivative a b (f n)) atTop K := by
  obtain ⟨R, _, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : PolarPoint)
  let C := spacesCompactCylinder R
  have hC : IsCompact C := spaces_isCompact_compactCylinder R
  let e (i j n : ℕ) := ∫ p in C, |mixedDerivative i j (f n) p - g i j p|
  let err (n : ℕ) := e a b n + e (a + 1) b n + e a (b + 1) n + e (a + 1) (b + 1) n
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa only [err, e, zero_add] using
      (((hlim a b C hC).add (hlim (a + 1) b C hC)).add (hlim a (b + 1) C hC)).add
        (hlim (a + 1) (b + 1) C hC)
  have hdiff (i j m n : ℕ) :
      (∫ p in C, |mixedDerivative i j (f m) p - mixedDerivative i j (f n) p|) ≤
        e i j m + e i j n := by
    have hmi : IntegrableOn (mixedDerivative i j (f m)) C volume :=
      (contDiff_mixedDerivative (hf m) i j).continuous.continuousOn.integrableOn_compact hC
    have hni : IntegrableOn (mixedDerivative i j (f n)) C volume :=
      (contDiff_mixedDerivative (hf n) i j).continuous.continuousOn.integrableOn_compact hC
    have hgi := (hg i j).integrableOn_isCompact hC
    have hsum : IntegrableOn
        (fun p => |mixedDerivative i j (f m) p - g i j p| +
          |mixedDerivative i j (f n) p - g i j p|) C volume :=
      (hmi.sub hgi).abs.add (hni.sub hgi).abs
    calc
      (∫ p in C, |mixedDerivative i j (f m) p - mixedDerivative i j (f n) p|) ≤
          ∫ p in C, |mixedDerivative i j (f m) p - g i j p| +
            |mixedDerivative i j (f n) p - g i j p| := by
        apply integral_mono (hmi.sub hni).abs hsum
        intro p
        simpa only [Pi.sub_apply, abs_sub_comm (g i j p)] using
          abs_sub_le (mixedDerivative i j (f m) p) (g i j p) (mixedDerivative i j (f n) p)
      _ = e i j m + e i j n := integral_add (hmi.sub hgi).abs (hni.sub hgi).abs
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (herr.eventually (gt_mem_nhds (half_pos hε)))
  refine ⟨N, fun m hm n hn p hpK => ?_⟩
  have hpx : |p.1| ≤ R := by
    have hpNorm : ‖p‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hKR hpK
    simpa only [Real.norm_eq_abs] using (norm_fst_le p).trans hpNorm
  let d : PolarPoint → ℝ := fun q => mixedDerivative a b (f m) q - mixedDerivative a b (f n) q
  have hmd := contDiff_mixedDerivative (hf m) a b
  have hnd := contDiff_mixedDerivative (hf n) a b
  have hd : ContDiff ℝ ∞ d := hmd.sub hnd
  have hdp (x : ℝ) : Function.Periodic (fun θ => d (x, θ)) Real.pi :=
    (mixedDerivative_angular_periodic (hp m) a b x).sub
      (mixedDerivative_angular_periodic (hp n) a b x)
  have hr : radialPartial d =
      fun q => mixedDerivative (a + 1) b (f m) q - mixedDerivative (a + 1) b (f n) q := by
    rw [spaces_radialPartial_sub hmd hnd, radialPartial_mixedDerivative (hf m),
      radialPartial_mixedDerivative (hf n)]
  have hθ : angularPartial d =
      fun q => mixedDerivative a (b + 1) (f m) q - mixedDerivative a (b + 1) (f n) q := by
    rw [spaces_angularPartial_sub hmd hnd, angularPartial_mixedDerivative (hf m),
      angularPartial_mixedDerivative (hf n)]
  have hrθ : radialPartial (angularPartial d) =
      fun q => mixedDerivative (a + 1) (b + 1) (f m) q -
        mixedDerivative (a + 1) (b + 1) (f n) q := by
    rw [hθ, spaces_radialPartial_sub (contDiff_mixedDerivative (hf m) a (b + 1))
      (contDiff_mixedDerivative (hf n) a (b + 1)), radialPartial_mixedDerivative (hf m),
      radialPartial_mixedDerivative (hf n)]
  have hpoint := spaces_abs_le_compactCylinder_L1 hd hdp hpx p.2
  rw [hrθ, hr, hθ] at hpoint
  have hcontrol : |d (p.1, p.2)| ≤ err m + err n := by
    refine hpoint.trans ((add_le_add (add_le_add (add_le_add
      (hdiff a b m n) (hdiff (a + 1) b m n))
      (hdiff a (b + 1) m n)) (hdiff (a + 1) (b + 1) m n)).trans_eq ?_)
    dsimp only [err]
    ring
  have hsum : err m + err n < ε := by linarith [hN m hm, hN n hn]
  simpa only [Real.dist_eq, d, Prod.eta] using hcontrol.trans_lt hsum

end ContinuousFlexibility.Statements
