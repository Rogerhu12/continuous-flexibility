import ContinuousFlexibility.Analysis.N04PositiveGeometryActualPhysicalHeightDirections
import ContinuousFlexibility.Analysis.N04PositiveGeometryActualHeightSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryControlledReferenceHeight
import ContinuousFlexibility.Analysis.N04PositiveGeometryTransportSamplePrefix
import ContinuousFlexibility.Analysis.N04PositiveGeometryAffineSpatialWords

/-!
# The actual physical height on the unit strip

The `Q` prefix and the inverse-transport prefix are aligned without
enlarging the parameter order. The fixed physical interval map adds
only a scalar coefficient before the normalized joint estimate.
-/

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set ContinuousFlexibility.Statements CanonicalGeometry
open scoped ContDiff

private theorem physicalUnitLinear_norm_le (l r C : ℝ)
    (hC : 1 ≤ C) (hspan : |r - l| ≤ C) :
    ‖((r - l) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (ContinuousLinearMap.snd ℝ ℝ ℝ)‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hC)
  intro v
  simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
    Prod.norm_def, norm_mul, Real.norm_eq_abs]
  refine max_le ?_ ?_
  · exact mul_le_mul hspan (le_max_left _ _) (abs_nonneg _) (zero_le_one.trans hC)
  · exact (le_max_right _ _).trans
      (le_mul_of_one_le_left (le_max_of_le_left (abs_nonneg _)) hC)

theorem n04PositiveGeometry_actualControlledUnitHeight_sample_prefix_of_inverseWords
    {W : N04RealizationStart} {X : N04RealizationChoice W} {order : ℕ}
    (G : N04PositiveGeometryControlledFamily W X order) (hn : order ≤ 3)
    (Y H₀ : N04PositiveComponent W.D.a W.D.b (deriv W.D.w) → ℝ → ℝ)
    (href : N04PositiveReferenceFamily (W.A X.e₀) X.src 4 Y H₀)
    (hmaterial : N04PositiveReferenceMaterialBounds W.T X.cell Y H₀)
    {base : ℕ} {ε : ℝ} (hb : W.base ≤ base) (hε : 0 < ε)
    (hεW : ε ≤ W.ε) (hεone : ε ≤ 1) (hGb : G.base ≤ base) (hGε : ε ≤ G.ε)
    (hflow : OrdinaryFlowJacobianBounds W.S W.C base ε)
    (hctx : ∀ m side,
      N04PositiveGeometryRootContext W.D W.S W.C (W.A X.e₀) base ε m side)
    (JS : ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
      SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ univ)
        (fun y : (StateDirections W.S × ℝ) × PolarPoint =>
          G.toN04PositiveGeometryControlData.σ (liftSectorParameter W.S W.C y.1) i y.2))
    (hσ : N04PositiveGeometryInverseTransportSamplePrefix G base ε) :
    ∃ low : ℕ, base ≤ low ∧ ∀ K : ℕ, ∃ shift : ℕ,
      ∀ s : ℕ, ∃ A : ℝ, 1 ≤ A ∧
      ∀ i : N04PositiveComponent W.D.a W.D.b (deriv W.D.w),
      ∀ J : SmoothDirections (sectorNeighborhood W.S base ε ε ×ˢ unitStrip)
        (fun y : (StateDirections W.S × ℝ) × PolarPoint =>
          n04PositiveGeometry_controlledUnitHeight G H₀ i (liftSectorParameter W.S W.C y.1) y.2),
      ∀ x ∈ sectorNeighborhood W.S base ε ε,
      pairGrading (sectorGrading W.S) realGrading low x ≤ 1 →
      ∀ q ∈ unitStrip, ∀ R : ℝ, 1 ≤ R →
      pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) x ≤ R →
      ∀ n : ℕ, 0 < n → n ≤ K + s → ∀ w : StateAngleWord n, w.stateArity ≤ K →
      ∀ v : Fin n → (StateDirections W.S × ℝ) × PolarPoint,
      (∀ j, if w.isState j then (v j).2 = 0 else (v j).1 = 0) →
      (∀ j, pairGrading (sectorGrading W.S) realGrading low (v j).1 ≤ 1 ∧
        pairGrading (sectorGrading W.S) realGrading (low + s + shift * K + 1) (v j).1 ≤ R ∧
        ‖(v j).2‖ ≤ 1) →
        ‖J.D n (x, q) v‖ ≤ A * W.U.E0 (W.U.sample (X.cell i)) ^ A *
          parameterHeightWeight (W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)) w.stateArity *
          R ^ (((w.angleArity + shift * w.stateArity : ℕ) : ℝ) /
            (((s + shift * K : ℕ) : ℝ) + 1)) := by
  obtain ⟨Lq, hLq, pq⟩ := n04PositiveGeometry_actualControlledHeight_sample_prefix
    G hn hb hε hεW hεone hGb hGε hflow hctx
  obtain ⟨Ls, _, ps⟩ := hσ
  obtain ⟨RH, _, hheight⟩ := n04PositiveGeometry_sample_height_bound W X
    (by norm_num : (0 : ℝ) < 3 / 4)
  let low := Lq + Ls
  have hql : Lq ≤ low := by dsimp only [low]; omega
  have hsl : Ls ≤ low := by dsimp only [low]; omega
  let C := max 1 (W.D.b - W.D.a)
  have hC : 1 ≤ C := le_max_left _ _
  refine ⟨low, hLq.trans hql, fun K => ?_⟩
  obtain ⟨cq, pqc⟩ := pq K
  obtain ⟨cs, psc⟩ := ps K
  let shift := cq + cs + 1
  have hcq : cq ≤ shift := by dsimp only [shift]; omega
  have hcs : cs ≤ shift := by dsimp only [shift]; omega
  have hcq1 : cq + 1 ≤ shift := by dsimp only [shift]; omega
  have hshift : 1 ≤ shift := by dsimp only [shift]; omega
  refine ⟨shift, fun s => ?_⟩
  obtain ⟨Aq, hAq, hqraw⟩ := pqc (s + (shift - cq) * K)
  obtain ⟨As, hAs, hsraw⟩ := psc (s + (shift - cs) * K)
  let A := max Aq As
  have hA : 1 ≤ A := hAq.trans (le_max_left _ _)
  obtain ⟨B, hB, hphysical⟩ := n04PositiveGeometry_controlledReferenceHeight_unit_word_bound
    (E := StateDirections W.S × ℝ) G Y H₀ href hmaterial (K + s) A RH
  obtain ⟨B₀, _, hpack⟩ := n04PositiveGeometry_polynomial_sample_pack (C ^ (K + s)) B 1
  let D := max 1 B₀
  have hD : 1 ≤ D := le_max_left _ _
  have hB₀D : B₀ ≤ D := le_max_right _ _
  refine ⟨D, hD, ?_⟩
  intro i J x hx hxlow q hq R hR hxR n hnpos hnN w hw v hpure hbox
  let p := pairGrading (sectorGrading W.S) realGrading
  have hp : Monotone p := sectorPairGrading_monotone W.S
  let E := W.U.E0 (W.U.sample (X.cell i))
  let H := W.U.H (W.U.sample (X.cell i)) ^ (3 / 4 : ℝ)
  let t := R ^ (1 / (((s + shift * K : ℕ) : ℝ) + 1))
  have hE : 1 ≤ E := (W.floor _).trans (le_enlargedMaterialData_E0 W.T _)
  have hH : 0 ≤ H := (hheight i).1
  have hAM : 0 ≤ A * E ^ A := mul_nonneg (zero_le_one.trans hA)
    (Real.rpow_nonneg (zero_le_one.trans hE) _)
  have ht : 1 ≤ t := Real.one_le_rpow hR (by positivity)
  have hcost {a : ℝ} (ha : a ≤ A) : a * E ^ a ≤ A * E ^ A :=
    mul_le_mul ha (Real.rpow_le_rpow_of_exponent_le hE ha)
      (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hA)
  have hden (c : ℕ) (hc : c ≤ shift) :
      s + (shift - c) * K + c * K = s + shift * K :=
    n04PositiveGeometry_prefix_horizon s K c shift hc
  have hhigh (l c : ℕ) (hl : l ≤ low) (hc : c ≤ shift) :
      l + (s + (shift - c) * K) + c * K + 1 ≤ low + s + shift * K + 1 := by
    have he := hden c hc
    omega
  have hsq : K + s ≤ s + (shift - cq) * K := by
    have hmul := Nat.mul_le_mul_right K (show 1 ≤ shift - cq by omega)
    omega
  have htpow (a : ℕ) : t ^ a = R ^ ((a : ℝ) / (((s + shift * K : ℕ) : ℝ) + 1)) := by
    dsimp only [t]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (zero_le_one.trans hR)]
    congr 1
    ring
  let JQ := n04PositiveGeometry_actualControlledHeight_joint G hn hb hε hεW hεone
    hGb hGε hflow hctx i true
  let RQ := n04PositiveGeometry_actualControlledHeight_mixedJetRegularity G hn hb hε hεW
    hεone hGb hGε hflow hctx i true
  let JP := n04PositiveGeometry_actualControlledPhysicalHeight_joint G hn Y H₀ href
    hb hε hεW hεone hGb hGε hflow hctx i (JS i)
  let l := n04PositiveLeft i
  let r := n04PositiveRight i
  let L : PolarPoint →L[ℝ] PolarPoint :=
    ((r - l) • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hpoint (y : PolarPoint) : (l, 0) + L y = (l + (r - l) * y.1, y.2) := by
    simp only [L, ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul,
      Prod.mk_add_mk, zero_add]
  have hgeo := n04PositiveComponent_bounds
    ((n04b_profileGeometry_of_through03 W.through03).2.2.1.1.continuous_deriv (by simp)) i
  have hrl : 0 < r - l := sub_pos.mpr hgeo.2.1
  have hL : ‖L‖ ≤ C := physicalUnitLinear_norm_le l r C hC (by
    rw [abs_of_pos hrl]
    exact (sub_le_sub hgeo.2.2 hgeo.1).trans (le_max_right _ _))
  have hqphys : (l, 0) + L q ∈ Ioo l r ×ˢ (univ : Set ℝ) := by
    rw [hpoint]
    refine ⟨⟨?_, ?_⟩, mem_univ _⟩
    · exact lt_add_of_pos_right l (mul_pos hrl hq.1.1)
    · have h := mul_lt_of_lt_one_right hrl hq.1.2
      linarith only [h]
  have hrawQ (k : ℕ) (hk : k ≤ K) (a b : ℕ) (hab : a + b + k ≤ K + s)
      (u : Fin k → (StateDirections W.S × ℝ))
      (hu : ∀ j, p low (u j) ≤ 1 ∧ p (low + s + shift * K + 1) (u j) ≤ R) :
      ‖(RQ.parameter a b (G.toN04PositiveGeometryControlData.σ
        (liftSectorParameter W.S W.C x) i ((l, 0) + L q)) (mem_univ _)).D k x u‖ ≤
        A * E ^ A * parameterHeightWeight H k * t ^ (a + b + shift * k) := by
    have h := hqraw i k hk a b (by omega) true
      (G.toN04PositiveGeometryControlData.σ (liftSectorParameter W.S W.C x) i ((l, 0) + L q))
      (RQ.parameter a b (G.toN04PositiveGeometryControlData.σ
        (liftSectorParameter W.S W.C x) i ((l, 0) + L q)) (mem_univ _)) x hx
      ((hp hql x).trans hxlow) u (fun j => (hp hql (u j)).trans (hu j).1) R hR
      ((hp (hhigh Lq cq hql hcq) x).trans hxR)
      (fun j => (hp (hhigh Lq cq hql hcq) (u j)).trans (hu j).2)
    exact h.trans (mul_le_mul
      (mul_le_mul_of_nonneg_right (hcost (le_max_left _ _)) (parameterHeightWeight_nonneg hH k))
      (n04PositiveGeometry_prefix_power_align s K (a + b) k cq shift hcq hR)
      (Real.rpow_nonneg (zero_le_one.trans hR) _)
      (mul_nonneg hAM (parameterHeightWeight_nonneg hH k)))
  have hrawS (j : ℕ) (hj : 0 < j) (hjN : j ≤ K + s) (u : StateAngleWord j)
      (hu : u.stateArity ≤ K) (a : Fin j → (StateDirections W.S × ℝ) × PolarPoint)
      (ha : ∀ k, if u.isState k then (a k).2 = 0 else (a k).1 = 0)
      (haB : ∀ k, p low (a k).1 ≤ 1 ∧
        p (low + s + shift * K + 1) (a k).1 ≤ R ∧ ‖(a k).2‖ ≤ 1) :
      ‖(JS i).D j (x, (l, 0) + L q) a‖ ≤ A * E ^ A * parameterHeightWeight H u.stateArity *
        t ^ (u.angleArity + shift * u.stateArity - 1) := by
    have h := hsraw i (JS i) x hx ((hp hsl x).trans hxlow) _ hqphys R hR
      ((hp (hhigh Ls cs hsl hcs) x).trans hxR) j hj (by omega) u hu a ha
      (fun k => ⟨(hp hsl (a k).1).trans (haB k).1,
        (hp (hhigh Ls cs hsl hcs) (a k).1).trans (haB k).2.1, (haB k).2.2⟩)
    apply h.trans
    have he := hden cs hcs
    rw [he]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (hcost (le_max_right _ _)) (parameterHeightWeight_nonneg hH _))
      (pow_le_pow_right₀ ht (Nat.sub_le_sub_right
        (Nat.add_le_add_left (Nat.mul_le_mul_right _ hcs) _) 1))
      (pow_nonneg (zero_le_one.trans ht) _) (mul_nonneg hAM (parameterHeightWeight_nonneg hH _))
  let JU := J.congrOn (fun y _ => congrArg
    (n04PositiveGeometry_controlledPhysicalHeight G H₀ i (liftSectorParameter W.S W.C y.1))
    (hpoint y.2).symm)
  have hout := n04PositiveGeometry_affineSpatial_word_bound JP
    (sectorNeighborhood_isOpen W.S base ε ε) (isOpen_Ioo.prod isOpen_univ) L (l, 0)
    (fun _ _ => mem_univ _) JU (p low) (p (low + s + shift * K + 1))
    hC hL (zero_le_one.trans hR) n w x hx q hq
    (fun u huL huH huS hu0 hu1 => hphysical
      (sectorNeighborhood W.S base ε ε) (sectorNeighborhood_isOpen W.S base ε ε)
      (sectorNeighborhood_convex W.S base ε ε) (liftSectorParameter W.S W.C) i false
      RQ JQ (JS i) JP x hx ((l, 0) + L q) (p low) (p (low + s + shift * K + 1))
      R (zero_le_one.trans hR) H t hH (hheight i).2 ht K shift hshift hrawQ hrawS
      n hnpos hnN w hw u
      (fun j => by
        cases hj : w.isState j with
        | false => simpa only [hj, if_false] using hu0 j hj
        | true => simpa only [hj, if_true] using hu1 j hj)
      (fun j => ⟨huL j, huH j, huS j⟩)) v
    (fun j => (hbox j).1) (fun j => (hbox j).2.1) (fun j => (hbox j).2.2)
    (fun j hj => by simpa only [hj, if_false] using hpure j)
    (fun j hj => by simpa only [hj, if_true] using hpure j)
  have hpack0 : C ^ (K + s) * (B * E ^ B) ≤ B₀ * E ^ B₀ := by
    simpa only [pow_one] using hpack E hE
  have hpack' : C ^ n * (B * E ^ B) ≤ D * E ^ D :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hnN)
      (mul_nonneg (zero_le_one.trans hB) (Real.rpow_nonneg (zero_le_one.trans hE) _))).trans
      (hpack0.trans (mul_le_mul hB₀D (Real.rpow_le_rpow_of_exponent_le hE hB₀D)
        (Real.rpow_nonneg (zero_le_one.trans hE) _) (zero_le_one.trans hD)))
  calc
    ‖J.D n (x, q) v‖ ≤ C ^ n * (B * E ^ B * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + shift * w.stateArity)) := hout
    _ = (C ^ n * (B * E ^ B)) * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + shift * w.stateArity) := by ring
    _ ≤ D * E ^ D * parameterHeightWeight H w.stateArity *
        t ^ (w.angleArity + shift * w.stateArity) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpack'
        (parameterHeightWeight_nonneg hH _)) (pow_nonneg (zero_le_one.trans ht) _)
    _ = _ := congrArg (fun v : ℝ => D * E ^ D * parameterHeightWeight H w.stateArity * v)
      (htpow (w.angleArity + shift * w.stateArity))

end ContinuousFlexibility.Analysis
