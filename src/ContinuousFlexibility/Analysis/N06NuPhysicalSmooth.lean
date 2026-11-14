module

public import ContinuousFlexibility.Analysis.N06NuCoordinateBounds

/-!
# Smoothness and finite symmetry calculus for the actual nu column

On its common compact radial support, the actual finite nu formula is
smooth by N01's positive discriminant. Outside that support the genuine
column vanishes on a neighborhood. Periodicity and angular reflection
follow from the actual height decoder and the same finite formula.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open scoped ContDiff

/-- Angular reflection changes the two odd polar height entries. -/
def n06NuCoordinateReflect (v : N06NuJetCoordinates) : N06NuJetCoordinates :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, -(v 7), -(v 8), v 9, v 10, v 11]

private theorem n06ResidualFiniteJetValue_reflect (r w w' a b c d e q : ℝ) :
    n06ResidualFiniteJetValue r w w' a b (-c) (-d) e q =
      n06ResidualFiniteJetValue r w w' a b c d e q := by
  simp only [n06ResidualFiniteJetValue, mul_neg, neg_sq]

private theorem n06NuFiniteJetValue_reflect (r w w' χ χ' a b c d e q ν : ℝ) :
    n06NuFiniteJetValue r w w' χ χ' a b (-c) (-d) e q ν =
      n06NuFiniteJetValue r w w' χ χ' a b c d e q ν := by
  apply congrArg (fun f : ℝ → ℝ => deriv f ν)
  funext t
  exact n06ResidualFiniteJetValue_reflect r (w * Real.exp (t * χ))
    ((w' + w * (t * χ')) * Real.exp (t * χ)) a b c d e q

theorem n06NuFiniteJetMap_reflect (v : N06NuJetCoordinates) :
    n06NuFiniteJetMap (n06NuCoordinateReflect v) = n06NuFiniteJetMap v := by
  change n06NuFiniteJetValue (v 0) (v 1) (v 2) (v 3) (v 4)
      (v 5) (v 6) (-v 7) (-v 8) (v 9) (v 10) (v 11) =
    n06NuFiniteJetValue (v 0) (v 1) (v 2) (v 3) (v 4)
      (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11)
  exact n06NuFiniteJetValue_reflect (v 0) (v 1) (v 2) (v 3) (v 4)
    (v 5) (v 6) (v 7) (v 8) (v 9) (v 10) (v 11)

end ContinuousFlexibility.Analysis

namespace ContinuousFlexibility.Statements

open Set Filter
open ContinuousFlexibility.Analysis
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {T : MaterialData} {S : PhysicalSpacesData}
  {C : NonlinearGeometryData S} {base loss : ℕ} {ε : ℝ}

theorem n06_stateU_periodic (hS : IsPhysicalSpaces D T S) (x : AnnularState S) :
    Function.Periodic (stateU S x) (0, Real.pi) := by
  have hp := ((hS.1 (3 / 4 : ℝ)).2.2.2.1 x.1.1).2.2.1
  intro p
  change (S.height (3 / 4 : ℝ)).decode x.1.1 (p + (0, Real.pi)) +
      x.1.2 * S.chiLeft (p + (0, Real.pi)).1 =
    (S.height (3 / 4 : ℝ)).decode x.1.1 p + x.1.2 * S.chiLeft p.1
  rw [hp p]
  simp only [Prod.fst_add, add_zero]

theorem n06_stateU_even (hS : IsPhysicalSpaces D T S) (x : AnnularState S) (p : PolarPoint) :
    stateU S x (p.1, -p.2) = stateU S x p := by
  have he := ((hS.1 (3 / 4 : ℝ)).2.2.2.1 x.1.1).2.1 p.1 p.2
  change (S.height (3 / 4 : ℝ)).decode x.1.1 (p.1, -p.2) + x.1.2 * S.chiLeft p.1 =
    (S.height (3 / 4 : ℝ)).decode x.1.1 p + x.1.2 * S.chiLeft p.1
  rw [he]

theorem n06_actualNuJetCoordinates_contDiffAt
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hw : ContDiff ℝ ∞ D.w) (hχ : ContDiff ℝ ∞ D.chi)
    (z : AnnularState S × ℝ) {p : PolarPoint} (hr : p.1 ≠ 0) :
    ContDiffAt ℝ ∞ (n06ActualNuJetCoordinates D S z) p := by
  have hu : ContDiffAt ℝ ∞ (stateU S z.1) p :=
    (neighborhood_stateU_contDiff (D := D) (T := T) (S := S) hT hS z.1).contDiffAt
  have hur : ContDiffAt ℝ ∞ (radialPartial (stateU S z.1)) p :=
    contDiffAt_radialPartial hu (by simp)
  have hurr : ContDiffAt ℝ ∞ (radialPartial (radialPartial (stateU S z.1))) p :=
    contDiffAt_radialPartial hur (by simp)
  have hut : ContDiffAt ℝ ∞ (heightAngular (stateU S z.1)) p :=
    contDiffAt_heightAngular hu (by simp) hr
  have hurt : ContDiffAt ℝ ∞ (radialPartial (heightAngular (stateU S z.1))) p :=
    contDiffAt_radialPartial hut (by simp)
  have hutt : ContDiffAt ℝ ∞ (angularPartial (heightAngular (stateU S z.1))) p :=
    contDiffAt_angularPartial hut (by simp)
  have hwr := (contDiff_infty_iff_deriv.mp hw).2
  have hχr := (contDiff_infty_iff_deriv.mp hχ).2
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;>
    simp only [n06ActualNuJetCoordinates, Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
    first | exact contDiffAt_fst | exact hw.contDiffAt.comp p contDiffAt_fst |
      exact hwr.contDiffAt.comp p contDiffAt_fst |
      exact hχ.contDiffAt.comp p contDiffAt_fst |
      exact hχr.contDiffAt.comp p contDiffAt_fst |
      exact hur | exact hurr | exact hut | exact hurt | exact hutt | exact contDiffAt_const

/-- In fact the actual nu column is globally smooth: its common compact
support lies strictly inside the annulus, where the finite formula applies. -/
theorem n06_nuColumn_contDiff
    (hT : IsMaterialData D T) (hS : IsPhysicalSpaces D T S)
    (hN01 : N01Properties D T S C base loss ε)
    {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
    (hs : stateSector S z.1) : ContDiff ℝ ∞ (nuColumnField D S C z) := by
  have hb : RadialTrueBorder D := hN01.1.2.2.2.1
  apply contDiff_iff_contDiffAt.mpr
  intro p
  by_cases hborder : p.1 ∈ tsupport D.chi
  · have hp : p ∈ annularOpen D := ⟨(hb.2.2.1 hborder).1, mem_univ _⟩
    have hr : p.1 ≠ 0 := (hN01.1.1.choose_spec.1.1.trans hp.1.1).ne'
    have hcoords := n06_actualNuJetCoordinates_contDiffAt hT hS
      hN01.1.1.choose_spec.1.2.2.1.1 hb.1 z hr
    have hpos : 0 < n06NuFiniteDiscriminant (n06ActualNuJetCoordinates D S z p) :=
      lt_of_lt_of_le (by norm_num)
        (n06_actualNuJetDiscriminant_lower hT hS hN01 hz hs hp hborder)
    have hfinite := (n06NuFiniteJetMap_contDiffAt hpos).comp p hcoords
    apply hfinite.congr_of_eventuallyEq
    filter_upwards [(isOpen_Ioo.prod isOpen_univ).mem_nhds hp] with q hq
    exact n06_nuColumn_eq_finiteJetMap hT hS hN01 z hq
  · apply contDiffAt_const.congr_of_eventuallyEq
    have hnear : ∀ᶠ q : PolarPoint in 𝓝 p, q.1 ∉ tsupport D.chi :=
      (hb.2.1.isClosed.isOpen_compl.preimage continuous_fst).mem_nhds hborder
    filter_upwards [hnear] with q hq
    exact n06_nuColumn_zero_off_tsupport hT hS hN01 z hq

private theorem n06_radial_coordinate_packet_periodic
    (f : Fin 5 → ℝ → ℝ) (g : Fin 7 → PolarPoint → ℝ)
    (hg : ∀ i, Function.Periodic (g i) (0, Real.pi)) :
    Function.Periodic (fun p : PolarPoint =>
      (![f 0 p.1, f 1 p.1, f 2 p.1, f 3 p.1, f 4 p.1,
        g 0 p, g 1 p, g 2 p, g 3 p, g 4 p, g 5 p, g 6 p] : N06NuJetCoordinates))
      (0, Real.pi) := by
  intro p
  ext i
  fin_cases i <;>
    simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Prod.fst_add, add_zero]
  all_goals first
  | exact hg 0 p
  | exact hg 1 p
  | exact hg 2 p
  | exact hg 3 p
  | exact hg 4 p
  | exact hg 5 p
  | exact hg 6 p
  | rfl

theorem n06_actualNuJetCoordinates_periodic
    (hS : IsPhysicalSpaces D T S) (z : AnnularState S × ℝ) :
    Function.Periodic (n06ActualNuJetCoordinates D S z) (0, Real.pi) := by
  have hu := n06_stateU_periodic hS z.1
  have hur := periodic_radialPartial hu
  have hurr := periodic_radialPartial hur
  have hut : Function.Periodic (heightAngular (stateU S z.1)) (0, Real.pi) := by
    intro p
    simp only [heightAngular, periodic_angularPartial hu p, Prod.fst_add, add_zero]
  have hurt := periodic_radialPartial hut
  have hutt := periodic_angularPartial hut
  let g : Fin 7 → PolarPoint → ℝ :=
    ![radialPartial (stateU S z.1), radialPartial (radialPartial (stateU S z.1)),
      heightAngular (stateU S z.1), radialPartial (heightAngular (stateU S z.1)),
      angularPartial (heightAngular (stateU S z.1)), fun _ => z.2, fun _ => z.1.2.1]
  have hg : ∀ i : Fin 7, Function.Periodic (g i) (0, Real.pi) := by
    intro i
    fin_cases i
    · exact hur
    · exact hurr
    · exact hut
    · exact hurt
    · exact hutt
    · intro p; rfl
    · intro p; rfl
  exact n06_radial_coordinate_packet_periodic
    ![id, D.w, deriv D.w, D.chi, deriv D.chi] g hg

private theorem n06_mixedDerivative_neg_angle (f : PolarPoint → ℝ)
    (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (fun q => f (q.1, -q.2)) p =
      (-1 : ℝ) ^ b * mixedDerivative a b f (p.1, -p.2) := by
  have he (r : ℝ) : iteratedDeriv b (fun θ => f (r, -θ)) p.2 =
      (-1 : ℝ) ^ b * iteratedDeriv b (fun θ => f (r, θ)) (-p.2) := by
    simpa only [smul_eq_mul] using iteratedDeriv_comp_neg b (fun θ => f (r, θ)) p.2
  have hefun : (fun r => iteratedDeriv b (fun θ => f (r, -θ)) p.2) =
      (fun r => (-1 : ℝ) ^ b * iteratedDeriv b (fun θ => f (r, θ)) (-p.2)) :=
    funext he
  change iteratedDeriv a (fun r => iteratedDeriv b (fun θ => f (r, -θ)) p.2) p.1 =
    (-1 : ℝ) ^ b *
      iteratedDeriv a (fun r => iteratedDeriv b (fun θ => f (r, θ)) (-p.2)) p.1
  exact (congrArg (fun g : ℝ → ℝ => iteratedDeriv a g p.1) hefun).trans
    (iteratedDeriv_const_mul_field (n := a) (x := p.1) ((-1 : ℝ) ^ b)
      (fun r => iteratedDeriv b (fun θ => f (r, θ)) (-p.2)))

theorem n06_stateU_mixedDerivative_reflection
    (hS : IsPhysicalSpaces D T S) (x : AnnularState S) (a b : ℕ) (p : PolarPoint) :
    mixedDerivative a b (stateU S x) (p.1, -p.2) =
      (-1 : ℝ) ^ b * mixedDerivative a b (stateU S x) p := by
  have heq : (fun q => stateU S x (q.1, -q.2)) = stateU S x :=
    funext (n06_stateU_even hS x)
  simpa only [heq, neg_neg, Prod.eta] using
    n06_mixedDerivative_neg_angle (stateU S x) a b (p.1, -p.2)

def n06NuReflectionPacket (f : Fin 5 → ℝ) (c d : ℝ)
    (u : Fin 7 → ℝ) : N06NuJetCoordinates :=
  ![f 0, f 1, f 2, f 3, f 4, u 0, u 1, c * u 2,
    c * u 3 - d * u 2, c * u 4, u 5, u 6]

theorem n06_nu_reflection_packet (f : Fin 5 → ℝ) (c d : ℝ)
    (u v : Fin 7 → ℝ)
    (h₀ : v 0 = u 0) (h₁ : v 1 = u 1)
    (h₂ : v 2 = -(u 2)) (h₃ : v 3 = -(u 3))
    (h₄ : v 4 = u 4) (h₅ : v 5 = u 5) (h₆ : v 6 = u 6) :
    n06NuReflectionPacket f c d v = n06NuCoordinateReflect (n06NuReflectionPacket f c d u) := by
  funext i
  fin_cases i
  · change f 0 = f 0
    rfl
  · change f 1 = f 1
    rfl
  · change f 2 = f 2
    rfl
  · change f 3 = f 3
    rfl
  · change f 4 = f 4
    rfl
  · change v 0 = u 0
    exact h₀
  · change v 1 = u 1
    exact h₁
  · change c * v 2 = -(c * u 2)
    exact (congrArg (fun x : ℝ => c * x) h₂).trans (mul_neg c (u 2))
  · change c * v 3 - d * v 2 = -(c * u 3 - d * u 2)
    exact (congrArg₂ (fun x y : ℝ => c * x - d * y) h₃ h₂).trans (by ring)
  · change c * v 4 = c * u 4
    exact congrArg (fun x : ℝ => c * x) h₄
  · change v 5 = u 5
    exact h₅
  · change v 6 = u 6
    exact h₆


end ContinuousFlexibility.Statements
