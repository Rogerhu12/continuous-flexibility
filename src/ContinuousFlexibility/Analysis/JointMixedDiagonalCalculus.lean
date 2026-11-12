import ContinuousFlexibility.Analysis.JointJetSpatialRegularity
import ContinuousFlexibility.Analysis.PhysicalJetLinearity
import ContinuousFlexibility.Analysis.MaterialMixedMultiplier

/-!
# Actual mixed jets on one parameter line

Parameter differentiation along a fixed direction commutes with the
actual two spatial derivatives.  The resulting diagonal jets obey the
three-index Leibniz formula.  The formula keeps parameter order and
spatial order separate, which is needed when a fixed parameter order is
estimated uniformly at every spatial order.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Statements

open Set Filter ContinuousFlexibility.Analysis
open scoped ContDiff Topology BigOperators

/-- The local version of the actual two-coordinate Leibniz identity. -/
theorem mixedDerivative_mul_on_open
    {V : Set PolarPoint} {f g : PolarPoint → ℝ}
    (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V) (hg : ContDiffOn ℝ ∞ g V)
    (a b : ℕ) {p : PolarPoint} (hp : p ∈ V) :
    mixedDerivative a b (fun q => f q * g q) p =
      ∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        (b.choose j : ℝ) * (a.choose i : ℝ) *
          mixedDerivative i j f p * mixedDerivative (a - i) (b - j) g p := by
  have hnear : ∀ᶠ r in 𝓝 p.1, (r, p.2) ∈ V :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hV.mem_nhds hp)
  have hangle : (fun r => iteratedDeriv b (fun θ => f (r, θ) * g (r, θ)) p.2) =ᶠ[𝓝 p.1]
      (fun r => ∑ j ∈ Finset.range (b + 1), (b.choose j : ℝ) *
        iteratedDeriv j (fun θ => f (r, θ)) p.2 *
          iteratedDeriv (b - j) (fun θ => g (r, θ)) p.2) := by
    filter_upwards [hnear] with r hr
    have hfr : ContDiffAt ℝ ∞ (fun θ => f (r, θ)) p.2 :=
      (hf.contDiffAt (hV.mem_nhds hr)).comp p.2 (contDiffAt_const.prodMk contDiffAt_id)
    have hgr : ContDiffAt ℝ ∞ (fun θ => g (r, θ)) p.2 :=
      (hg.contDiffAt (hV.mem_nhds hr)).comp p.2 (contDiffAt_const.prodMk contDiffAt_id)
    exact iteratedDeriv_fun_mul (hfr.of_le (by simp)) (hgr.of_le (by simp))
  have hfr (j : ℕ) : ContDiffAt ℝ ∞
      (fun r => iteratedDeriv j (fun θ => f (r, θ)) p.2) p.1 := by
    have h := ((contDiffOn_mixedDerivative hV hf 0 j).contDiffAt
      (hV.mem_nhds hp)).comp p.1 (contDiffAt_id.prodMk contDiffAt_const)
    simpa only [mixedDerivative, iteratedDeriv_zero, Function.comp_def, id_eq] using h
  have hgr (j : ℕ) : ContDiffAt ℝ ∞
      (fun r => iteratedDeriv j (fun θ => g (r, θ)) p.2) p.1 := by
    have h := ((contDiffOn_mixedDerivative hV hg 0 j).contDiffAt
      (hV.mem_nhds hp)).comp p.1 (contDiffAt_id.prodMk contDiffAt_const)
    simpa only [mixedDerivative, iteratedDeriv_zero, Function.comp_def, id_eq] using h
  have hterm (j : ℕ) : ContDiffAt ℝ ∞ (fun r =>
      (b.choose j : ℝ) * iteratedDeriv j (fun θ => f (r, θ)) p.2 *
        iteratedDeriv (b - j) (fun θ => g (r, θ)) p.2) p.1 :=
    (contDiffAt_const.mul (hfr j)).mul (hgr (b - j))
  unfold mixedDerivative
  rw [hangle.iteratedDeriv_eq a,
    iteratedDeriv_fun_sum (fun j _ => (hterm j).of_le (by simp))]
  apply Finset.sum_congr rfl
  intro j hj
  have heq : (fun r => (b.choose j : ℝ) *
      iteratedDeriv j (fun θ => f (r, θ)) p.2 *
        iteratedDeriv (b - j) (fun θ => g (r, θ)) p.2) =
      (fun r => (b.choose j : ℝ) *
        (iteratedDeriv j (fun θ => f (r, θ)) p.2 *
          iteratedDeriv (b - j) (fun θ => g (r, θ)) p.2)) := by
    funext r
    ring
  rw [heq, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_mul ((hfr j).of_le (by simp)) ((hgr (b - j)).of_le (by simp)),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end ContinuousFlexibility.Statements

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : Set PolarPoint} {f : E × PolarPoint → ℝ}

/-- Actual spatial derivatives of a pure, repeated parameter jet. -/
def jointMixedDiagonal (J : SmoothDirections (U ×ˢ V) f)
    (n a b : ℕ) (x w : E) (p : PolarPoint) : ℝ :=
  mixedDerivative a b (fun q => J.D n (x, q) (fun _ => (w, (0 : PolarPoint)))) p

theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.spatial_value_contDiffOn
    (J : SmoothDirections (U ×ˢ V) f) (hV : IsOpen V) (x : E) (hx : x ∈ U) :
    ContDiffOn ℝ ∞ (fun p => f (x, p)) V := by
  apply (J.jointJet_spatial_contDiffOn hV 0 x hx Fin.elim0).congr
  intro p hp
  exact (J.zero (x, p) ⟨hx, hp⟩).symm

theorem jointMixedDiagonal_zero
    (J : SmoothDirections (U ×ˢ V) f) (hV : IsOpen V)
    (a b : ℕ) (x w : E) (hx : x ∈ U) {p : PolarPoint} (hp : p ∈ V) :
    jointMixedDiagonal J 0 a b x w p = mixedDerivative a b (fun q => f (x, q)) p := by
  apply mixedDerivative_congr_on_open hV _ a b hp
  intro q hq
  have hv : (fun _ : Fin 0 => (w, (0 : PolarPoint))) = Fin.elim0 := Subsingleton.elim _ _
  rw [hv]
  exact J.zero (x, q) ⟨hx, hq⟩

theorem jointMixedDiagonal_hasDerivAt_line
    (J : SmoothDirections (U ×ˢ V) f)
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (n a b : ℕ) (x w : E) {t : ℝ} (ht : x + t • w ∈ U)
    {p : PolarPoint} (hp : p ∈ V) :
    HasDerivAt (fun s => jointMixedDiagonal J n a b (x + s • w) w p)
      (jointMixedDiagonal J (n + 1) a b (x + t • w) w p) t := by
  have h := J.jointJet_mixed_hasDerivAt_line hU hV hc a b n x w ht
    (fun _ => (w, (0 : PolarPoint))) hp
  have hv : Fin.cons (w, (0 : PolarPoint)) (fun _ : Fin n => (w, (0 : PolarPoint))) =
      (fun _ : Fin (n + 1) => (w, (0 : PolarPoint))) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  simpa only [jointMixedDiagonal, hv] using h

theorem jointMixedDiagonal_line_contDiffOn
    (J : SmoothDirections (U ×ˢ V) f)
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (n a b : ℕ) (x w : E) {p : PolarPoint} (hp : p ∈ V) :
    ContDiffOn ℝ ∞ (fun t => jointMixedDiagonal J n a b (x + t • w) w p)
      ((fun t : ℝ => x + t • w) ⁻¹' U) := by
  let I : Set ℝ := (fun t : ℝ => x + t • w) ⁻¹' U
  have hI : IsOpen I := hU.preimage
    (show Continuous (fun t : ℝ => x + t • w) from
      continuous_const.add (continuous_id.smul continuous_const))
  let g : ℕ → ℝ → ℝ := fun k t => jointMixedDiagonal J k a b (x + t • w) w p
  have hd (k : ℕ) (t : ℝ) (ht : t ∈ I) : HasDerivAt (g k) (g (k + 1) t) t :=
    jointMixedDiagonal_hasDerivAt_line J hU hV hc k a b x w ht hp
  have hfinite : ∀ l k : ℕ, ContDiffOn ℝ l (g k) I := by
    intro l
    induction l with
    | zero =>
        intro k
        exact contDiffOn_zero.mpr (fun t ht => (hd k t ht).continuousAt.continuousWithinAt)
    | succ l ih =>
        intro k t ht
        apply ContDiffAt.contDiffWithinAt
        apply contDiffAt_succ_iff_hasFDerivAt.mpr
        refine ⟨fun s => ContinuousLinearMap.toSpanSingleton ℝ (g (k + 1) s),
          ⟨I, hI.mem_nhds ht, fun s hs => (hd k s hs).hasFDerivAt⟩, ?_⟩
        have heq : (fun s => ContinuousLinearMap.toSpanSingleton ℝ (g (k + 1) s)) =
            (fun s => g (k + 1) s • ContinuousLinearMap.id ℝ ℝ) := by
          funext s
          apply ContinuousLinearMap.ext
          intro y
          simp only [ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.id_apply, smul_eq_mul]
          ring
        rw [heq]
        exact ((ih (k + 1)).contDiffAt (hI.mem_nhds ht)).smul contDiffAt_const
  intro t ht
  exact (contDiffAt_infty.mpr (fun l =>
    (hfinite l n).contDiffAt (hI.mem_nhds ht))).contDiffWithinAt

theorem jointMixedDiagonal_eq_iteratedDeriv
    (J : SmoothDirections (U ×ˢ V) f)
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (n a b : ℕ) (x w : E) {t : ℝ} (ht : x + t • w ∈ U)
    {p : PolarPoint} (hp : p ∈ V) :
    iteratedDeriv n (fun s => mixedDerivative a b (fun q => f (x + s • w, q)) p) t =
      jointMixedDiagonal J n a b (x + t • w) w p := by
  induction n generalizing t with
  | zero =>
      rw [iteratedDeriv_zero]
      exact (jointMixedDiagonal_zero J hV a b (x + t • w) w ht hp).symm
  | succ n ih =>
      have hnear : ∀ᶠ s in 𝓝 t, x + s • w ∈ U :=
        (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.eventually
          (hU.mem_nhds ht)
      have heq : iteratedDeriv n
          (fun s => mixedDerivative a b (fun q => f (x + s • w, q)) p) =ᶠ[𝓝 t]
          (fun s => jointMixedDiagonal J n a b (x + s • w) w p) := by
        filter_upwards [hnear] with s hs
        exact ih hs
      rw [iteratedDeriv_succ, heq.deriv_eq]
      exact (jointMixedDiagonal_hasDerivAt_line J hU hV hc n a b x w ht hp).deriv

theorem _root_.ContinuousFlexibility.Statements.SmoothDirections.mixed_actual_line_contDiffOn
    (J : SmoothDirections (U ×ˢ V) f)
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (a b : ℕ) (x w : E) {p : PolarPoint} (hp : p ∈ V) :
    ContDiffOn ℝ ∞ (fun t => mixedDerivative a b (fun q => f (x + t • w, q)) p)
      ((fun t : ℝ => x + t • w) ⁻¹' U) := by
  apply (jointMixedDiagonal_line_contDiffOn J hU hV hc 0 a b x w hp).congr
  intro t ht
  exact (jointMixedDiagonal_zero J hV a b (x + t • w) w ht hp).symm

theorem jointMixedDiagonal_congr
    {g : E × PolarPoint → ℝ} (J : SmoothDirections (U ×ˢ V) f)
    (K : SmoothDirections (U ×ˢ V) g) (hV : IsOpen V)
    (heq : EqOn f g (U ×ˢ V)) (n a b : ℕ)
    (x w : E) (hx : x ∈ U) {p : PolarPoint} (hp : p ∈ V) :
    jointMixedDiagonal J n a b x w p = jointMixedDiagonal K n a b x w p := by
  apply mixedDerivative_congr_on_open hV _ a b hp
  intro q hq
  exact congrArg (fun A : (E × PolarPoint) [×n]→L[ℝ] ℝ =>
    A (fun _ => (w, (0 : PolarPoint))))
    ((J.congrOn heq).unique K n (x, q) ⟨hx, hq⟩)

/-- Three independent Leibniz indices: parameter, radius, and angle.
Every term uses exactly the original spatial order `a + b`. -/
theorem jointMixedDiagonal_mul
    {g h : E × PolarPoint → ℝ}
    (J : SmoothDirections (U ×ˢ V) f) (K : SmoothDirections (U ×ˢ V) g)
    (L : SmoothDirections (U ×ˢ V) h)
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (hprod : ∀ x ∈ U, ∀ p ∈ V, h (x, p) = f (x, p) * g (x, p))
    (n a b : ℕ) (x w : E) (hx : x ∈ U) {p : PolarPoint} (hp : p ∈ V) :
    jointMixedDiagonal L n a b x w p =
      ∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        ∑ k ∈ Finset.range (n + 1),
          (b.choose j : ℝ) * (a.choose i : ℝ) * (n.choose k : ℝ) *
            jointMixedDiagonal J k i j x w p *
              jointMixedDiagonal K (n - k) (a - i) (b - j) x w p := by
  let I : Set ℝ := (fun t : ℝ => x + t • w) ⁻¹' U
  have hI : IsOpen I := hU.preimage
    (show Continuous (fun t : ℝ => x + t • w) from
      continuous_const.add (continuous_id.smul continuous_const))
  have hz : (0 : ℝ) ∈ I := by simpa only [I, mem_preimage, zero_smul, add_zero] using hx
  have hfr (i j : ℕ) : ContDiffAt ℝ ∞
      (fun t : ℝ => mixedDerivative i j (fun q => f (x + t • w, q)) p) 0 :=
    (J.mixed_actual_line_contDiffOn hU hV hc i j x w hp).contDiffAt (hI.mem_nhds hz)
  have hgr (i j : ℕ) : ContDiffAt ℝ ∞
      (fun t : ℝ => mixedDerivative i j (fun q => g (x + t • w, q)) p) 0 :=
    (K.mixed_actual_line_contDiffOn hU hV hc i j x w hp).contDiffAt (hI.mem_nhds hz)
  have hterm (j i : ℕ) : ContDiffAt ℝ ∞ (fun t : ℝ =>
      (b.choose j : ℝ) * (a.choose i : ℝ) *
        mixedDerivative i j (fun q => f (x + t • w, q)) p *
          mixedDerivative (a - i) (b - j) (fun q => g (x + t • w, q)) p) 0 :=
    (contDiffAt_const.mul (hfr i j)).mul (hgr (a - i) (b - j))
  have heq : (fun t : ℝ => mixedDerivative a b (fun q => h (x + t • w, q)) p) =ᶠ[𝓝 0]
      (fun t : ℝ => ∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        (b.choose j : ℝ) * (a.choose i : ℝ) *
          mixedDerivative i j (fun q => f (x + t • w, q)) p *
            mixedDerivative (a - i) (b - j) (fun q => g (x + t • w, q)) p) := by
    filter_upwards [hI.mem_nhds hz] with t ht
    exact (mixedDerivative_congr_on_open hV (fun q hq => hprod _ ht q hq) a b hp).trans
      (mixedDerivative_mul_on_open hV (J.spatial_value_contDiffOn hV _ ht)
        (K.spatial_value_contDiffOn hV _ ht) a b hp)
  have hL : jointMixedDiagonal L n a b x w p =
      iteratedDeriv n (fun t : ℝ => mixedDerivative a b (fun q => h (x + t • w, q)) p) 0 := by
    simpa only [zero_smul, add_zero] using
      (jointMixedDiagonal_eq_iteratedDeriv L hU hV hc n a b x w hz hp).symm
  rw [hL, heq.iteratedDeriv_eq n,
    iteratedDeriv_fun_sum (fun j _ =>
      (ContDiffAt.sum (fun i _ => hterm j i)).of_le (by simp))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [iteratedDeriv_fun_sum (fun i _ => (hterm j i).of_le (by simp))]
  apply Finset.sum_congr rfl
  intro i hi
  have hgroup : (fun t : ℝ => (b.choose j : ℝ) * (a.choose i : ℝ) *
      mixedDerivative i j (fun q => f (x + t • w, q)) p *
        mixedDerivative (a - i) (b - j) (fun q => g (x + t • w, q)) p) =
      (fun t : ℝ => ((b.choose j : ℝ) * (a.choose i : ℝ)) *
        (mixedDerivative i j (fun q => f (x + t • w, q)) p *
          mixedDerivative (a - i) (b - j) (fun q => g (x + t • w, q)) p)) := by
    funext t
    ring
  rw [hgroup, iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_mul ((hfr i j).of_le (by simp))
      ((hgr (a - i) (b - j)).of_le (by simp)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [jointMixedDiagonal_eq_iteratedDeriv J hU hV hc k i j x w hz hp,
    jointMixedDiagonal_eq_iteratedDeriv K hU hV hc (n - k) (a - i) (b - j) x w hz hp]
  simp only [zero_smul, add_zero]
  ring

theorem jointMixedDiagonal_radial_step
    (J : SmoothDirections (U ×ˢ V) f) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (n a b : ℕ) (x w : E) (hx : x ∈ U) {p : PolarPoint} (hp : p ∈ V) :
    jointMixedDiagonal J n (a + 1) b x w p =
      jointMixedDiagonal (J.fixedLast (0, (1, 0))) n a b x w p :=
  J.jointJet_mixed_radial_step hV hc a b n x hx (fun _ => (w, 0)) hp

theorem jointMixedDiagonal_angular_step
    (J : SmoothDirections (U ×ˢ V) f) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (n a b : ℕ) (x w : E) (hx : x ∈ U) {p : PolarPoint} (hp : p ∈ V) :
    jointMixedDiagonal J n a (b + 1) x w p =
      jointMixedDiagonal (J.fixedLast (0, (0, 1))) n a b x w p :=
  J.jointJet_mixed_angular_step hV hc a b n x hx (fun _ => (w, 0)) hp

end ContinuousFlexibility.Analysis
