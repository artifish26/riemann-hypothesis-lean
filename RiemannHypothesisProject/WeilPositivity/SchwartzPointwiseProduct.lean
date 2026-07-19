import RiemannHypothesisProject.SchwartzLineTestFunction

/-!
# Jointly continuous pointwise products on Schwartz line tests

Mathlib packages multiplication by one fixed temperate function as a
continuous linear map.  For the Weil quadratic form both factors vary.  This
module proves the required joint continuity directly from the defining
Schwartz seminorms.
-/

namespace RiemannHypothesisProject

namespace SchwartzLineTestFunction

noncomputable section

/-- Pointwise multiplication of two Schwartz line tests. -/
def pointwiseProduct
    (f g : SchwartzLineTestFunction) : SchwartzLineTestFunction :=
  SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul Real Complex)
    g.hasTemperateGrowth f

@[simp]
theorem pointwiseProduct_apply
    (f g : SchwartzLineTestFunction) (x : Real) :
    pointwiseProduct f g x = f x * g x := by
  simp [pointwiseProduct, SchwartzMap.bilinLeftCLM_apply]

theorem pointwiseProduct_add_left
    (f g h : SchwartzLineTestFunction) :
    pointwiseProduct (f + g) h =
      pointwiseProduct f h + pointwiseProduct g h := by
  ext x
  simp [add_mul]

theorem pointwiseProduct_add_right
    (f g h : SchwartzLineTestFunction) :
    pointwiseProduct f (g + h) =
      pointwiseProduct f g + pointwiseProduct f h := by
  ext x
  simp [mul_add]

theorem pointwiseProduct_sub_left
    (f g h : SchwartzLineTestFunction) :
    pointwiseProduct (f - g) h =
      pointwiseProduct f h - pointwiseProduct g h := by
  ext x
  simp [sub_mul]

theorem pointwiseProduct_sub_right
    (f g h : SchwartzLineTestFunction) :
    pointwiseProduct f (g - h) =
      pointwiseProduct f g - pointwiseProduct f h := by
  ext x
  simp [mul_sub]

/-- Every output seminorm of a pointwise product is bounded by the finite
Leibniz sum of input seminorm products. -/
theorem seminorm_pointwiseProduct_le
    (k n : Nat) (f g : SchwartzLineTestFunction) :
    SchwartzMap.seminorm Real k n (pointwiseProduct f g) <=
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : Real) * SchwartzMap.seminorm Real k i f *
          SchwartzMap.seminorm Real 0 (n - i) g := by
  apply SchwartzMap.seminorm_le_bound
  · positivity
  intro x
  have hderiv := ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (ContinuousLinearMap.mul Real Complex)
    (f.smooth ⊤) (g.smooth ⊤) x (n := n) (mod_cast le_top)
    (ContinuousLinearMap.opNorm_mul_le Real Complex)
  change
    ‖x‖ ^ k *
        ‖iteratedFDeriv Real n (fun y : Real => f y * g y) x‖ <= _
  calc
    _ <= ‖x‖ ^ k *
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : Real) * ‖iteratedFDeriv Real i f x‖ *
            ‖iteratedFDeriv Real (n - i) g x‖ := by
      gcongr
      simpa only [ContinuousLinearMap.mul_apply'] using hderiv
    _ = ∑ i ∈ Finset.range (n + 1),
        (n.choose i : Real) *
          (‖x‖ ^ k * ‖iteratedFDeriv Real i f x‖) *
            ‖iteratedFDeriv Real (n - i) g x‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ <= ∑ i ∈ Finset.range (n + 1),
        (n.choose i : Real) * SchwartzMap.seminorm Real k i f *
          SchwartzMap.seminorm Real 0 (n - i) g := by
      apply Finset.sum_le_sum
      intro i hi
      have hfi := SchwartzMap.le_seminorm Real k i f x
      have hgi := SchwartzMap.norm_iteratedFDeriv_le_seminorm
        (𝕜 := Real) g (n - i) x
      gcongr

/-- Pointwise multiplication is jointly continuous for the Schwartz
topology, not merely continuous after one factor has been fixed. -/
theorem continuous_pointwiseProduct :
    Continuous (fun p : SchwartzLineTestFunction × SchwartzLineTestFunction =>
      pointwiseProduct p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [ContinuousAt,
    (schwartz_withSeminorms Real Real Complex).tendsto_nhds]
  rintro ⟨k, n⟩ ε hε
  let q (a b : Nat) : SchwartzLineTestFunction → Real :=
    SchwartzMap.seminorm Real a b
  let firstBound
      (r : SchwartzLineTestFunction × SchwartzLineTestFunction) : Real :=
    ∑ i ∈ Finset.range (n + 1),
      (n.choose i : Real) * q k i (r.1 - p.1) * q 0 (n - i) r.2
  let secondBound
      (r : SchwartzLineTestFunction × SchwartzLineTestFunction) : Real :=
    ∑ i ∈ Finset.range (n + 1),
      (n.choose i : Real) * q k i p.1 * q 0 (n - i) (r.2 - p.2)
  have hq (a b : Nat) : Continuous (q a b) :=
    (schwartz_withSeminorms Real Real Complex).continuous_seminorm (a, b)
  have hfirst : Filter.Tendsto firstBound (nhds p) (nhds 0) := by
    have hsum : Filter.Tendsto
        (fun r => ∑ i ∈ Finset.range (n + 1),
          (n.choose i : Real) * q k i (r.1 - p.1) * q 0 (n - i) r.2)
        (nhds p) (nhds (∑ _i ∈ Finset.range (n + 1), (0 : Real))) := by
      apply tendsto_finsetSum
      intro i hi
      have hleft : Filter.Tendsto
          (fun r : SchwartzLineTestFunction × SchwartzLineTestFunction =>
            q k i (r.1 - p.1)) (nhds p) (nhds 0) := by
        have hsub : Continuous
            (fun r : SchwartzLineTestFunction × SchwartzLineTestFunction =>
              r.1 - p.1) :=
          continuous_fst.sub continuous_const
        have hc : Continuous
            (fun r : SchwartzLineTestFunction × SchwartzLineTestFunction =>
              q k i (r.1 - p.1)) :=
          (hq k i).comp hsub
        simpa only [q, sub_self, map_zero] using hc.tendsto p
      have hright : Filter.Tendsto
          (fun r : SchwartzLineTestFunction × SchwartzLineTestFunction =>
            q 0 (n - i) r.2) (nhds p) (nhds (q 0 (n - i) p.2)) :=
        ((hq 0 (n - i)).comp continuous_snd).continuousAt
      simpa using
        (tendsto_const_nhds.mul hleft).mul hright
    simpa [firstBound] using hsum
  have hsecond : Filter.Tendsto secondBound (nhds p) (nhds 0) := by
    have hsum : Filter.Tendsto
        (fun r => ∑ i ∈ Finset.range (n + 1),
          (n.choose i : Real) * q k i p.1 * q 0 (n - i) (r.2 - p.2))
        (nhds p) (nhds (∑ _i ∈ Finset.range (n + 1), (0 : Real))) := by
      apply tendsto_finsetSum
      intro i hi
      have hright : Filter.Tendsto
          (fun r : SchwartzLineTestFunction × SchwartzLineTestFunction =>
            q 0 (n - i) (r.2 - p.2)) (nhds p) (nhds 0) := by
        have hsub : Continuous
            (fun r : SchwartzLineTestFunction × SchwartzLineTestFunction =>
              r.2 - p.2) :=
          continuous_snd.sub continuous_const
        have hc : Continuous
            (fun r : SchwartzLineTestFunction × SchwartzLineTestFunction =>
              q 0 (n - i) (r.2 - p.2)) :=
          (hq 0 (n - i)).comp hsub
        simpa only [q, sub_self, map_zero] using hc.tendsto p
      simpa using
        (tendsto_const_nhds.mul tendsto_const_nhds).mul hright
    simpa [secondBound] using hsum
  have htotal : Filter.Tendsto (fun r => firstBound r + secondBound r)
      (nhds p) (nhds 0) := by
    simpa using hfirst.add hsecond
  have heventually : ∀ᶠ r in nhds p, firstBound r + secondBound r < ε :=
    (tendsto_order.1 htotal).2 ε hε
  filter_upwards [heventually] with r hr
  have hdecomp :
      pointwiseProduct r.1 r.2 - pointwiseProduct p.1 p.2 =
        pointwiseProduct (r.1 - p.1) r.2 +
          pointwiseProduct p.1 (r.2 - p.2) := by
    ext x
    simp [sub_mul, mul_sub]
  rw [hdecomp]
  calc
    _ <= SchwartzMap.seminorm Real k n
          (pointwiseProduct (r.1 - p.1) r.2) +
        SchwartzMap.seminorm Real k n
          (pointwiseProduct p.1 (r.2 - p.2)) :=
      map_add_le_add (SchwartzMap.seminorm Real k n) _ _
    _ <= firstBound r + secondBound r := by
      apply add_le_add
      · simpa [q, firstBound] using
          seminorm_pointwiseProduct_le k n (r.1 - p.1) r.2
      · simpa [q, secondBound] using
          seminorm_pointwiseProduct_le k n p.1 (r.2 - p.2)
    _ < ε := hr

end

end SchwartzLineTestFunction

end RiemannHypothesisProject
