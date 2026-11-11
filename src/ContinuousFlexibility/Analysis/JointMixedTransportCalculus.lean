import ContinuousFlexibility.Analysis.JointMixedDiagonalCalculus
import ContinuousFlexibility.Analysis.SmoothDirectionsNormedComposition

/-!
# Actual mixed transport recurrences

The transport identities are differentiated in the parameter, radius,
and angle.  The finite sums below are the actual derivatives of genuine
joint towers.  Their indices record separately the parameter order and
the two spatial orders; no formal jet is substituted for a derivative.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ContinuousFlexibility.Analysis

open Set Filter ContinuousFlexibility.Statements
open scoped ContDiff Topology BigOperators

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  {U : Set E} {V : Set PolarPoint} {f g h : E × PolarPoint → ℝ}

theorem jointMixedDiagonal_add
    (J : SmoothDirections (U ×ˢ V) f) (K : SmoothDirections (U ×ˢ V) g)
    (L : SmoothDirections (U ×ˢ V) h) (hV : IsOpen V)
    (heq : ∀ x ∈ U, ∀ p ∈ V, h (x, p) = f (x, p) + g (x, p))
    (n a b : ℕ) (x w : E) (hx : x ∈ U) {p : PolarPoint} (hp : p ∈ V) :
    jointMixedDiagonal L n a b x w p =
      jointMixedDiagonal J n a b x w p + jointMixedDiagonal K n a b x w p := by
  have he := jointMixedDiagonal_congr L (smoothDirectionsAdd J K) hV
    (fun y hy => heq y.1 hy.1 y.2 hy.2) n a b x w hx hp
  have hJ := J.jointJet_spatial_contDiffOn hV n x hx (fun _ => (w, (0 : PolarPoint)))
  have hK := K.jointJet_spatial_contDiffOn hV n x hx (fun _ => (w, (0 : PolarPoint)))
  have hs := mixedDerivative_sub_of_contDiffOn hV hJ
    ((contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : PolarPoint => (-1 : ℝ)) V).mul hK)
    a b hp
  have hfun : (fun q => J.D n (x, q) (fun _ => (w, (0 : PolarPoint))) -
      (-1) * K.D n (x, q) (fun _ => (w, (0 : PolarPoint)))) =
      (fun q => J.D n (x, q) (fun _ => (w, (0 : PolarPoint))) +
        K.D n (x, q) (fun _ => (w, (0 : PolarPoint)))) := by
    funext q
    ring
  rw [hfun, mixedDerivative_const_mul] at hs
  exact he.trans (by
    simpa only [jointMixedDiagonal, smoothDirectionsAdd, ContinuousMultilinearMap.add_apply,
      neg_one_mul, sub_neg_eq_add] using hs)

theorem jointMixedDiagonal_const_mul
    (J : SmoothDirections (U ×ˢ V) f) (K : SmoothDirections (U ×ˢ V) g)
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (c : ℝ) (heq : ∀ x ∈ U, ∀ p ∈ V, g (x, p) = c * f (x, p))
    (n a b : ℕ) (x w : E) (hx : x ∈ U) {p : PolarPoint} (hp : p ∈ V) :
    jointMixedDiagonal K n a b x w p = c * jointMixedDiagonal J n a b x w p := by
  have hz : x + (0 : ℝ) • w ∈ U := by simpa only [zero_smul, add_zero] using hx
  have hnear : ∀ᶠ t : ℝ in 𝓝 0, x + t • w ∈ U :=
    (continuous_const.add (continuous_id.smul continuous_const)).continuousAt.eventually
      (by simpa only [zero_smul, add_zero] using hU.mem_nhds hx)
  have he : (fun t => mixedDerivative a b (fun q => g (x + t • w, q)) p) =ᶠ[𝓝 0]
      (fun t => c * mixedDerivative a b (fun q => f (x + t • w, q)) p) := by
    filter_upwards [hnear] with t ht
    exact (mixedDerivative_congr_on_open hV (fun q hq => heq _ ht q hq) a b hp).trans
      (mixedDerivative_const_mul c _ a b p)
  have hK := jointMixedDiagonal_eq_iteratedDeriv K hU hV hc n a b x w hz hp
  have hJ := jointMixedDiagonal_eq_iteratedDeriv J hU hV hc n a b x w hz hp
  simp only [zero_smul, add_zero] at hK hJ
  rw [← hK, he.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, hJ]

theorem jointMixedDiagonal_sub
    (J : SmoothDirections (U ×ˢ V) f) (K : SmoothDirections (U ×ˢ V) g)
    (L : SmoothDirections (U ×ˢ V) h)
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (heq : ∀ x ∈ U, ∀ p ∈ V, h (x, p) = f (x, p) - g (x, p))
    (n a b : ℕ) (x w : E) (hx : x ∈ U) {p : PolarPoint} (hp : p ∈ V) :
    jointMixedDiagonal L n a b x w p =
      jointMixedDiagonal J n a b x w p - jointMixedDiagonal K n a b x w p := by
  let I : Set ℝ := (fun t : ℝ => x + t • w) ⁻¹' U
  have hI : IsOpen I := hU.preimage
    (show Continuous (fun t : ℝ => x + t • w) from
      continuous_const.add (continuous_id.smul continuous_const))
  have hz : (0 : ℝ) ∈ I := by simpa only [I, mem_preimage, zero_smul, add_zero] using hx
  have hf : ContDiffAt ℝ ∞
      (fun t => mixedDerivative a b (fun q => f (x + t • w, q)) p) 0 :=
    (J.mixed_actual_line_contDiffOn hU hV hc a b x w hp).contDiffAt (hI.mem_nhds hz)
  have hg : ContDiffAt ℝ ∞
      (fun t => mixedDerivative a b (fun q => g (x + t • w, q)) p) 0 :=
    (K.mixed_actual_line_contDiffOn hU hV hc a b x w hp).contDiffAt (hI.mem_nhds hz)
  have he : (fun t => mixedDerivative a b (fun q => h (x + t • w, q)) p) =ᶠ[𝓝 0]
      (fun t => mixedDerivative a b (fun q => f (x + t • w, q)) p -
        mixedDerivative a b (fun q => g (x + t • w, q)) p) := by
    filter_upwards [hI.mem_nhds hz] with t ht
    exact (mixedDerivative_congr_on_open hV (fun q hq => heq _ ht q hq) a b hp).trans
      (mixedDerivative_sub_of_contDiffOn hV (J.spatial_value_contDiffOn hV _ ht)
        (K.spatial_value_contDiffOn hV _ ht) a b hp)
  have hL := jointMixedDiagonal_eq_iteratedDeriv L hU hV hc n a b x w hz hp
  have hJ := jointMixedDiagonal_eq_iteratedDeriv J hU hV hc n a b x w hz hp
  have hK := jointMixedDiagonal_eq_iteratedDeriv K hU hV hc n a b x w hz hp
  simp only [zero_smul, add_zero] at hL hJ hK
  rw [← hL, he.iteratedDeriv_eq n,
    iteratedDeriv_fun_sub (hf.of_le (by simp)) (hg.of_le (by simp)), hJ, hK]

theorem SmoothDirections.radialPartial_value_eq_fixedLast
    (J : SmoothDirections (U ×ˢ V) f) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (x : E) (hx : x ∈ U) {p : PolarPoint} (hp : p ∈ V) :
    radialPartial (fun q => f (x, q)) p =
      J.D 1 (x, p) (fun _ => (0, (1, 0))) := by
  have he : (fun q => J.D 0 (x, q) Fin.elim0) =ᶠ[𝓝 p] (fun q => f (x, q)) := by
    filter_upwards [hV.mem_nhds hp] with q hq
    exact J.zero (x, q) ⟨hx, hq⟩
  have he' : radialPartial (fun q => J.D 0 (x, q) Fin.elim0) p =
      radialPartial (fun q => f (x, q)) p := by
    exact congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (1, 0)) (he.fderiv_eq (𝕜 := ℝ))
  have hs := J.jointJet_radialPartial_eq_fixedLast hc 0 x hx Fin.elim0 hp
  rw [(J.fixedLast (0, (1, 0))).zero (x, p) ⟨hx, hp⟩] at hs
  exact he'.symm.trans hs

theorem SmoothDirections.angularPartial_value_eq_fixedLast
    (J : SmoothDirections (U ×ˢ V) f) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (x : E) (hx : x ∈ U) {p : PolarPoint} (hp : p ∈ V) :
    angularPartial (fun q => f (x, q)) p =
      J.D 1 (x, p) (fun _ => (0, (0, 1))) := by
  have he : (fun q => J.D 0 (x, q) Fin.elim0) =ᶠ[𝓝 p] (fun q => f (x, q)) := by
    filter_upwards [hV.mem_nhds hp] with q hq
    exact J.zero (x, q) ⟨hx, hq⟩
  have he' : angularPartial (fun q => J.D 0 (x, q) Fin.elim0) p =
      angularPartial (fun q => f (x, q)) p := by
    exact congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (0, 1)) (he.fderiv_eq (𝕜 := ℝ))
  have hs := J.jointJet_angularPartial_eq_fixedLast hc 0 x hx Fin.elim0 hp
  rw [(J.fixedLast (0, (0, 1))).zero (x, p) ⟨hx, hp⟩] at hs
  exact he'.symm.trans hs

/-- The genuine joint tower of the actual radial derivative. -/
def SmoothDirections.spatialRadialTower
    (J : SmoothDirections (U ×ˢ V) f) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V)) :
    SmoothDirections (U ×ˢ V) (fun z => radialPartial (fun q => f (z.1, q)) z.2) :=
  (J.fixedLast (0, (1, 0))).congrOn (fun z hz =>
    (J.radialPartial_value_eq_fixedLast hV hc z.1 hz.1 hz.2).symm)

/-- The genuine joint tower of the actual angular derivative. -/
def SmoothDirections.spatialAngularTower
    (J : SmoothDirections (U ×ˢ V) f) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V)) :
    SmoothDirections (U ×ˢ V) (fun z => angularPartial (fun q => f (z.1, q)) z.2) :=
  (J.fixedLast (0, (0, 1))).congrOn (fun z hz =>
    (J.angularPartial_value_eq_fixedLast hV hc z.1 hz.1 hz.2).symm)

theorem jointMixedDiagonal_spatialRadial
    (J : SmoothDirections (U ×ˢ V) f) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (n a b : ℕ) (x w : E) (hx : x ∈ U) {p : PolarPoint} (hp : p ∈ V) :
    jointMixedDiagonal (J.spatialRadialTower hV hc) n a b x w p =
      jointMixedDiagonal J n (a + 1) b x w p :=
  (jointMixedDiagonal_radial_step J hV hc n a b x w hx hp).symm

theorem jointMixedDiagonal_spatialAngular
    (J : SmoothDirections (U ×ˢ V) f) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (n a b : ℕ) (x w : E) (hx : x ∈ U) {p : PolarPoint} (hp : p ∈ V) :
    jointMixedDiagonal (J.spatialAngularTower hV hc) n a b x w p =
      jointMixedDiagonal J n a (b + 1) x w p :=
  (jointMixedDiagonal_angular_step J hV hc n a b x w hx hp).symm

/-- The exact mixed recurrence for a transported scalar.  Every factor
on the right has radial order at most `a`. -/
theorem jointMixedDiagonal_transport
    (J : SmoothDirections (U ×ˢ V) f) (K : SmoothDirections (U ×ˢ V) g)
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (htransport : ∀ x ∈ U, ∀ p ∈ V,
      radialPartial (fun q => f (x, q)) p =
        -(g (x, p) * angularPartial (fun q => f (x, q)) p))
    (n a b : ℕ) (x w : E) (hx : x ∈ U) {p : PolarPoint} (hp : p ∈ V) :
    jointMixedDiagonal J n (a + 1) b x w p =
      -(∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        ∑ k ∈ Finset.range (n + 1),
          (b.choose j : ℝ) * (a.choose i : ℝ) * (n.choose k : ℝ) *
            jointMixedDiagonal K k i j x w p *
              jointMixedDiagonal J (n - k) (a - i) (b - j + 1) x w p) := by
  let Jθ := J.spatialAngularTower hV hc
  let Jr := J.spatialRadialTower hV hc
  let L := K.mul Jθ
  have hneg : ∀ y ∈ U, ∀ q ∈ V,
      radialPartial (fun s => f (y, s)) q =
        (-1 : ℝ) * (g (y, q) * angularPartial (fun s => f (y, s)) q) := by
    intro y hy q hq
    rw [htransport y hy q hq]
    ring
  have hlinear := jointMixedDiagonal_const_mul L Jr hU hV hc (-1) hneg n a b x w hx hp
  have hprod := jointMixedDiagonal_mul K Jθ L hU hV hc
    (fun _ _ _ _ => rfl) n a b x w hx hp
  have hs := jointMixedDiagonal_spatialRadial J hV hc n a b x w hx hp
  rw [← hs, hlinear, hprod, neg_one_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  rw [jointMixedDiagonal_spatialAngular J hV hc (n - k) (a - i) (b - j) x w hx hp]

/-- The variational transport equation is differentiated with the same
three-index Leibniz coefficients. -/
theorem jointMixedDiagonal_variational_transport
    (J : SmoothDirections (U ×ˢ V) f) (K : SmoothDirections (U ×ˢ V) g)
    (hU : IsOpen U) (hV : IsOpen V) (hc : Convex ℝ (U ×ˢ V))
    (htransport : ∀ x ∈ U, ∀ p ∈ V,
      radialPartial (fun q => f (x, q)) p =
        angularPartial (fun q => g (x, q)) p * f (x, p) -
          g (x, p) * angularPartial (fun q => f (x, q)) p)
    (n a b : ℕ) (x w : E) (hx : x ∈ U) {p : PolarPoint} (hp : p ∈ V) :
    jointMixedDiagonal J n (a + 1) b x w p =
      (∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        ∑ k ∈ Finset.range (n + 1),
          (b.choose j : ℝ) * (a.choose i : ℝ) * (n.choose k : ℝ) *
            jointMixedDiagonal K k i (j + 1) x w p *
              jointMixedDiagonal J (n - k) (a - i) (b - j) x w p) -
      (∑ j ∈ Finset.range (b + 1), ∑ i ∈ Finset.range (a + 1),
        ∑ k ∈ Finset.range (n + 1),
          (b.choose j : ℝ) * (a.choose i : ℝ) * (n.choose k : ℝ) *
            jointMixedDiagonal K k i j x w p *
              jointMixedDiagonal J (n - k) (a - i) (b - j + 1) x w p) := by
  let Jθ := J.spatialAngularTower hV hc
  let Kθ := K.spatialAngularTower hV hc
  let Jr := J.spatialRadialTower hV hc
  let L₁ := Kθ.mul J
  let L₂ := K.mul Jθ
  have hsub := jointMixedDiagonal_sub L₁ L₂ Jr hU hV hc htransport n a b x w hx hp
  have h₁ := jointMixedDiagonal_mul Kθ J L₁ hU hV hc
    (fun _ _ _ _ => rfl) n a b x w hx hp
  have h₂ := jointMixedDiagonal_mul K Jθ L₂ hU hV hc
    (fun _ _ _ _ => rfl) n a b x w hx hp
  have hs := jointMixedDiagonal_spatialRadial J hV hc n a b x w hx hp
  rw [← hs, hsub, h₁, h₂]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro k hk
    rw [jointMixedDiagonal_spatialAngular K hV hc k i j x w hx hp]
  · apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro k hk
    rw [jointMixedDiagonal_spatialAngular J hV hc (n - k) (a - i) (b - j) x w hx hp]

end ContinuousFlexibility.Analysis
