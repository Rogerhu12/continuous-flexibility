module

public import ContinuousFlexibility.Analysis.N08CharacteristicFactors
public import ContinuousFlexibility.Analysis.N08FlowUniqueness

/-!
# Locality of the actual flow and return on one negative component

The angle bound and the continuous-endpoint uniqueness theorem identify
the actual ordinary flows.  The two inverse identities from N02 then
identify the chosen inverse return and inverse right chart.  Thus the
given residual, not a replacement candidate, has component locality.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Statements

open Set
open ContinuousFlexibility.Analysis
open scoped ContDiff

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {R : ReturnEquationData S}
  {base loss : ℕ} {ε : ℝ}

theorem n08_minusFlow_component_eq_of_speed
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {x y : AnnularState S} {q q' : ℝ} {m : ℕ}
    (hx : (x, q) ∈ stateNeighborhood S C base ε)
    (hy : (y, q') ∈ stateNeighborhood S C base ε) (hsx : stateSector S x)
    (hspeed : ∀ r ∈ Ioo (C.left m) (C.right m), ∀ θ,
      minusCharacteristicSpeed (originalCoefficients D S C (x, q)) (r, θ) =
        minusCharacteristicSpeed (originalCoefficients D S C (y, q')) (r, θ))
    (θ : ℝ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) :
    C.minusFlow (x, q) m r θ = C.minusFlow (y, q') m r θ := by
  have hgeom : RadialProfileGeometry D := hN.1.1.choose_spec.1
  have hdata := hN
  obtain ⟨_, _, _, hcontrol, _, _, hflow, _, _, hadmiss, _⟩ := hdata
  have hb := hcontrol.1 m
  have hfx := hflow (x, q) hx m θ
  have hfy := hflow (y, q') hy m θ
  let f : ℝ → ℝ := fun t => C.minusFlow (x, q) m t θ
  let g : ℝ → ℝ := fun t => C.minusFlow (y, q') m t θ
  have hfc : ContinuousOn f (Icc (C.left m) (C.right m)) := hfx.2.1
  have hgc : ContinuousOn g (Icc (C.left m) (C.right m)) := hfy.2.1
  obtain ⟨Mf, hMf⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  obtain ⟨Mg, hMg⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  let L : ℝ := max Mf Mg
  have hfL (t : ℝ) (ht : t ∈ Icc (C.left m) (C.right m)) : f t ∈ Icc (-L) L := by
    have hnorm : |f t| ≤ Mf := by simpa only [Real.norm_eq_abs] using hMf t ht
    exact abs_le.mp (hnorm.trans (le_max_left _ _))
  have hgL (t : ℝ) (ht : t ∈ Icc (C.left m) (C.right m)) : g t ∈ Icc (-L) L := by
    have hnorm : |g t| ≤ Mg := by simpa only [Real.norm_eq_abs] using hMg t ht
    exact abs_le.mp (hnorm.trans (le_max_right _ _))
  let w : ℝ → ℝ := stateProfile D S C x
  let h : PolarPoint → ℝ := stateHeight D S C (x, q)
  have hw : ContDiff ℝ ∞ w := contDiff_stateProfile_of_n01 hS hT hN x
  have hh : ContDiff ℝ ∞ h :=
    ((n08_stateRadialHeight_contDiff hT hS hN x).comp contDiff_fst).add
      (contDiff_const.mul (n08_stateU_contDiff hT hS x))
  have hpos (p : PolarPoint) (hp : p ∈ Icc (C.left m) (C.right m) ×ˢ Icc (-L) L) :
      0 < polarDiscriminant w h p ∧
        0 < heightQ (profileEnergy w p) (heightRadial h p) (angularPartial (heightAngular h) p) := by
    have hcore : p.1 ∈ radialCore D := ⟨hb.1.trans_le hp.1.1, hp.1.2.trans_lt hb.2.2⟩
    obtain ⟨hwlo, _, hQlo, _, hDlo, _⟩ := hadmiss (x, q) hx hsx p ⟨hcore, mem_univ _⟩
    have hwp : 0 < w p.1 := (div_pos_iff_of_pos_right (hgeom.2.2.2.2.1 p.1 hcore)).mp
      (lt_of_lt_of_le (by norm_num) hwlo)
    exact ⟨lt_of_lt_of_le (by norm_num) hDlo,
      (div_pos_iff_of_pos_right hwp).mp (lt_of_lt_of_le (by norm_num) hQlo)⟩
  obtain ⟨K, _, hK⟩ := n08JacobiMinusSpeed_angle_bound hw hh (hgeom.1.trans hb.1)
    (fun p hp => (hpos p hp).1) (fun p hp => (hpos p hp).2)
  have hdf (t : ℝ) (ht : t ∈ Ioo (C.left m) (C.right m)) :
      HasDerivAt f (n08JacobiMinusSpeed w h (t, f t)) t := hfx.2.2.1 t ht
  have hdg (t : ℝ) (ht : t ∈ Ioo (C.left m) (C.right m)) :
      HasDerivAt g (n08JacobiMinusSpeed w h (t, g t)) t := by
    have he := hspeed t ht (g t)
    exact (hfy.2.2.1 t ht).congr_deriv he.symm
  have heq := n08_scalarTrajectory_unique hb.2.1.le hfc hgc hdf hdg
    (fun t ht => hK t (Ioo_subset_Icc_self ht)
      (f t) (hfL t (Ioo_subset_Icc_self ht)) (g t) (hgL t (Ioo_subset_Icc_self ht)))
    (hfx.1.trans hfy.1.symm)
  exact heq hr

theorem n08_minusFlow_component_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    {x y : AnnularState S} {q : ℝ} {m : ℕ}
    (hx : (x, q) ∈ stateNeighborhood S C base ε)
    (hy : (y, q) ∈ stateNeighborhood S C base ε) (hsx : stateSector S x)
    (hheight : x.1 = y.1) (hν : x.2.1 = y.2.1)
    (hκ : stateKappa S x m = stateKappa S y m)
    (θ : ℝ) {r : ℝ} (hr : r ∈ Icc (C.left m) (C.right m)) :
    C.minusFlow (x, q) m r θ = C.minusFlow (y, q) m r θ :=
  n08_minusFlow_component_eq_of_speed hT hS hN hx hy hsx
    (fun _ ht θ => n08_minusCharacteristicSpeed_component_eq hT hS hN
      hheight hν hκ q ht θ) θ hr

theorem n08_returnResidualField_component_eq_of_flow
    (hR : N02Properties D T S C R base ε)
    {x y : AnnularState S} {q q' : ℝ} {m : ℕ}
    (hx : (x, q) ∈ stateNeighborhood S C base ε)
    (hy : (y, q') ∈ stateNeighborhood S C base ε)
    (hsx : stateSector S x) (hsy : stateSector S y)
    (hf : ∀ η, C.minusFlow (x, q) m (C.right m) η =
      C.minusFlow (y, q') m (C.right m) η)
    (hchart : stateLeftChart S x m = stateLeftChart S y m) (θ : ℝ) :
    returnResidualField S C (x, q) m θ = returnResidualField S C (y, q') m θ := by
  have hi (η : ℝ) : C.minusReturnInverse (x, q) m η = C.minusReturnInverse (y, q') m η := by
    have hyi := (hR.1 (y, q') hy hsy m (C.minusReturnInverse (x, q) m η)).2.1
    rw [← hf, (hR.1 (x, q) hx hsx m η).1] at hyi
    exact hyi.symm
  have hc : rightChartCandidate S C (x, q) m = rightChartCandidate S C (y, q') m := by
    funext η
    simp only [rightChartCandidate, oddPart, hi, hchart]
  have hri (η : ℝ) : C.rightChartInverse (x, q) m η = C.rightChartInverse (y, q') m η := by
    have hyi := (hR.1 (y, q') hy hsy m (C.rightChartInverse (x, q) m η)).2.2.2.1
    rw [← hc, (hR.1 (x, q) hx hsx m η).2.2.1] at hyi
    exact hyi.symm
  simp only [returnResidualField, evenPart, hi, hchart, hri]

theorem n08_returnResidualField_component_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    {x y : AnnularState S} {q : ℝ} {m : ℕ}
    (hx : (x, q) ∈ stateNeighborhood S C base ε)
    (hy : (y, q) ∈ stateNeighborhood S C base ε)
    (hsx : stateSector S x) (hsy : stateSector S y)
    (hheight : x.1 = y.1) (hν : x.2.1 = y.2.1)
    (hκ : stateKappa S x m = stateKappa S y m)
    (hchart : stateLeftChart S x m = stateLeftChart S y m) (θ : ℝ) :
    returnResidualField S C (x, q) m θ = returnResidualField S C (y, q) m θ :=
  n08_returnResidualField_component_eq_of_flow hR hx hy hsx hsy
    (fun η => n08_minusFlow_component_eq hT hS hN hx hy hsx hheight hν hκ η
      ⟨(hN.2.2.2.1.1 m).2.1.le, le_rfl⟩) hchart θ

theorem n08_returnResidual_component_eq
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN : N01Properties D T S C base loss ε)
    (hR : N02Properties D T S C R base ε)
    {x y : AnnularState S} {q : ℝ} {m : ℕ}
    (hx : (x, q) ∈ stateNeighborhood S C base ε)
    (hy : (y, q) ∈ stateNeighborhood S C base ε)
    (hsx : stateSector S x) (hsy : stateSector S y)
    (hheight : x.1 = y.1) (hν : x.2.1 = y.2.1)
    (hκ : stateKappa S x m = stateKappa S y m)
    (hchart : stateLeftChart S x m = stateLeftChart S y m) (θ : ℝ) :
    (S.circle (3 / 4 : ℝ)).decode (R.residual (x, q)) m θ =
      (S.circle (3 / 4 : ℝ)).decode (R.residual (y, q)) m θ := by
  rw [hR.2.1 (x, q) hx hsx m θ, hR.2.1 (y, q) hy hsy m θ]
  exact n08_returnResidualField_component_eq hT hS hN hR hx hy hsx hsy hheight hν hκ hchart θ

end ContinuousFlexibility.Statements
