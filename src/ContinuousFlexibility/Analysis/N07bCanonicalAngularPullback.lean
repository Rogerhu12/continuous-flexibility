module

public import ContinuousFlexibility.Analysis.N07bDirectionChain

/-!
# Actual angular jets of arbitrary canonical fields

The pullback recursion is valid for every smooth field on the canonical
open piece. It does not require a globally smooth physical source, so it
also applies to reference forcing whose representative is only finitely
smooth across the interfaces.
-/

@[expose] public section

noncomputable section

namespace ContinuousFlexibility.Analysis

open Set Filter
open ContinuousFlexibility.Statements ContinuousFlexibility.Blueprint
open scoped ContDiff Topology

set_option backward.isDefEq.respectTransparency false

variable {D : ReferenceData} {S : PhysicalSpacesData} {C : NonlinearGeometryData S}
  {K : CanonicalData S} {base : ℕ} {ε : ℝ}
  (hK : N04PartA D S C K base ε)
  {z : AnnularState S × ℝ} (hz : z ∈ stateNeighborhood S C base ε)
  (hs : stateSector S z.1)

include hK hz hs

/-- Open-piece physical smoothness suffices for the actual source formula
to be smooth on the canonical open piece. No interface jets are assumed. -/
theorem n07b_contDiffOn_canonicalSource_of_open (m : ℕ) {f : PolarPoint → ℝ}
    (hf : ContDiffOn ℝ ∞ f (physicalPieceOpen S K z m)) :
    ContDiffOn ℝ ∞ (canonicalSource S K z m f) (canonicalOpen S K m) := by
  have hcharts := hK.charts z hz hs m
  have hU : IsOpen (physicalPieceOpen S K z m) := (hK.domains z hz hs m).1
  have hV : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  intro p hp
  have hx := hcharts.2.1 hp
  have hraw := n07b_contDiffAt_physicalSourceFactor hK hz hs m
    (subset_closure hx) ((hf _ hx).contDiffAt (hU.mem_nhds hx))
  have hinv : ContDiffAt ℝ ∞ (K.inverseChart z m) p :=
    hcharts.2.2.2.2.2.1.contDiffAt (hV.mem_nhds hp)
  change ContDiffWithinAt ℝ ∞
    ((fun x => K.height z m x * f x / |planeJacobian (K.chart z m) x|) ∘
      K.inverseChart z m) (canonicalOpen S K m) p
  exact (hraw.comp p hinv).contDiffWithinAt

/-- Exact angular pullback for every smooth canonical field. Every
iteration is the derivative of the actual preceding physical expression. -/
theorem n07b_canonicalAngularJet_comp_chart (m : ℕ) {g : PolarPoint → ℝ}
    (hg : ContDiffOn ℝ ∞ g (canonicalOpen S K m)) (j : ℕ)
    {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K z m) :
    mixedDerivative 0 j g (K.chart z m x) =
      n07bDirectionIterate (fun _ => n07bInverseAngleVector (K.chart z m))
        (g ∘ K.chart z m) j x := by
  have hcharts := hK.charts z hz hs m
  have hU : IsOpen (physicalPieceOpen S K z m) := (hK.domains z hz hs m).1
  have hV : IsOpen (canonicalOpen S K m) := isOpen_Ioo.prod isOpen_univ
  have hphys : ContDiffOn ℝ ∞ (g ∘ K.chart z m) (physicalPieceOpen S K z m) :=
    hg.comp hcharts.2.2.2.2.1 hcharts.1
  have hX : ContDiffOn ℝ ∞ (n07bInverseAngleVector (K.chart z m))
      (physicalPieceOpen S K z m) := by
    intro y hy
    exact (n07b_contDiffAt_inverseAngleVector
      (hcharts.2.2.2.2.1.contDiffAt (hU.mem_nhds hy))
      (hcharts.2.2.2.2.2.2.2 y hy).2.1).contDiffWithinAt
  induction j generalizing x with
  | zero => simp only [mixedDerivative, iteratedDeriv_zero, n07bDirectionIterate,
      Function.comp_apply, Prod.eta]
  | succ j ih =>
      have heq : EqOn (mixedDerivative 0 j g)
          (n07bDirectionIterate (fun _ => n07bInverseAngleVector (K.chart z m))
            (g ∘ K.chart z m) j ∘ K.inverseChart z m) (canonicalOpen S K m) := by
        intro p hp
        have h := ih (x := K.inverseChart z m p) (hcharts.2.1 hp)
        rw [hcharts.2.2.2.1 p hp] at h
        exact h
      have hevent : mixedDerivative 0 j g =ᶠ[𝓝 (K.chart z m x)]
          (n07bDirectionIterate (fun _ => n07bInverseAngleVector (K.chart z m))
            (g ∘ K.chart z m) j ∘ K.inverseChart z m) := by
        filter_upwards [hV.mem_nhds (hcharts.1 hx)] with p hp
        exact heq hp
      have hd : DifferentiableAt ℝ
          (n07bDirectionIterate (fun _ => n07bInverseAngleVector (K.chart z m))
            (g ∘ K.chart z m) j) x :=
        (n07bDirectionIterate_contDiffAt
          (fun _ => (hX x hx).contDiffAt (hU.mem_nhds hx))
          ((hphys x hx).contDiffAt (hU.mem_nhds hx)) j).differentiableAt (by simp)
      calc
        _ = angularPartial (mixedDerivative 0 j g) (K.chart z m x) :=
          (angularPartial_mixedDerivative_on_open hV hg 0 j (hcharts.1 hx)).symm
        _ = angularPartial
            (n07bDirectionIterate (fun _ => n07bInverseAngleVector (K.chart z m))
              (g ∘ K.chart z m) j ∘ K.inverseChart z m) (K.chart z m x) :=
          congrArg (fun L : PolarPoint →L[ℝ] ℝ => L (0, 1)) (hevent.fderiv_eq (𝕜 := ℝ))
        _ = _ := n07b_canonical_angularPartial_comp_inverse hK hz hs m hx hd

/-- Any actual physical formula for the zeroth pullback may be used in
the recursion, provided it agrees on the whole open piece. -/
theorem n07b_canonicalAngularJet_eq_directionChain (m : ℕ)
    {g f : PolarPoint → ℝ}
    (hg : ContDiffOn ℝ ∞ g (canonicalOpen S K m))
    (hfg : EqOn (g ∘ K.chart z m) f (physicalPieceOpen S K z m))
    (j : ℕ) {x : PolarPoint} (hx : x ∈ physicalPieceOpen S K z m) :
    mixedDerivative 0 j g (K.chart z m x) =
      n07bDirectionIterate (fun _ => n07bInverseAngleVector (K.chart z m)) f j x := by
  rw [n07b_canonicalAngularJet_comp_chart hK hz hs m hg j hx]
  exact n07bDirectionIterate_congr _ (hK.domains z hz hs m).1 hfg j hx

end ContinuousFlexibility.Analysis
