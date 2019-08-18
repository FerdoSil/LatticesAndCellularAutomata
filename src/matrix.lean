import grid utils data.vector2

open utils

namespace matrix

structure matrix (m n : ℕ) (α : Type) :=
  (g  : agrid₀ α)
  (hr : g.r = m)
  (hc : g.c = n)

section operations

variables {m n o p : ℕ} {α β γ δ : Type}

def matrix_string [has_to_string α] (m : matrix m n α) :=
  grid_str m.g

instance matrix_repr [has_to_string α] : has_repr (matrix m n α) :=
  ⟨matrix_string⟩

instance matrix_to_string [has_to_string α] : has_to_string (matrix m n α) :=
  ⟨matrix_string⟩

instance matrix_functor : functor (matrix m n) := {
  map := λα β f m,
    ⟨f <$> m.g, by rw [agrid_fmap_r, m.hr], by rw [agrid_fmap_c, m.hc]⟩
}

instance matrix_functor_law : is_lawful_functor (matrix m n) := {
  id_map := λα ⟨⟨⟨r, c, h, d⟩, o⟩, hr, hc⟩, by simp [(<$>), vector.map_id],
  comp_map := λα β γ f h ⟨⟨⟨r, c, h, d⟩, o⟩, hr, hc⟩, by simp [(<$>)]
}

def m₁ : matrix 5 2 ℕ :=
  matrix.mk
    (agrid₀.mk ⟨5, 2, dec_trivial, ⟨[1, 3, 4, 5, 7, 8, 9, 10, 11, 12], dec_trivial⟩⟩ ⟨5, 1⟩)
    rfl rfl

def m₂ : matrix 2 3 ℕ :=
  matrix.mk
    (agrid₀.mk ⟨2, 3, dec_trivial, ⟨[2, 2, 2, 2, 2, 2], dec_trivial⟩⟩ ⟨0, 0⟩)
    rfl rfl

def transpose (m₁ : matrix m n α) : matrix n m α :=
  ⟨(agrid_of_fgrid ⟨
      n, m, begin
              cases m₁ with g h₁ h₂,
              subst h₁, subst h₂,
              exact mul_comm g.r g.c ▸ g.h
            end, ⟨m₁.g.o.y - m, m₁.g.o.x + n⟩,
      λx y, abs_data m₁.g ⟨⟨y.1,
        begin
          cases y with y h, simp at h, simp [expand_gtr, grid.bl],
          have : ↑(relative_grid.rows (m₁.g)) = ↑m,
            {
              cases m₁ with g h₁ h₂, cases g, simp at h₁ h₂,
              subst h₁, subst h₂, simp [relative_grid.rows]
            },
          rw this, exact h
        end⟩, ⟨x.1,
        begin
          cases x with x h, simp at h, simp [expand_gtr, grid.bl],
          have : ↑(relative_grid.cols (m₁.g)) = ↑n,
            {
              cases m₁ with g h₁ h₂, cases g, simp at h₁ h₂,
              subst h₁, subst h₂, simp [relative_grid.cols]
            },
          rw this, exact h
        end⟩⟩⟩), by simp, by simp⟩

instance [has_add α] : has_add (matrix m n α) := {
  add := λm₁ m₂,
    matrix.mk (agrid₀.mk ⟨m, n, begin
                                  cases m₁ with g, cases g with g o, cases g, cc
                                end,
                        begin
                          cases m₁ with g₁ hr₁ hc₁,
                          cases g₁ with g₁ g₁o, cases g₁ with r₁ c₁ h₁ data₁,
                          cases m₂ with g₂ hr₂ hc₂,
                          cases g₂ with g₂ g₂o, cases g₂ with r₂ c₂ h₂ data₂,
                          simp at hr₁ hc₁ hr₂ hc₂,
                          subst hc₁, subst hr₁, subst hc₂, subst hr₂,
                          exact vector.zip_with (+) data₁ data₂
                        end⟩ ⟨0, 0⟩) rfl rfl
}

theorem transpose_transpose_id (m₁ : matrix m n α) :
  transpose (transpose m₁) = m₁ :=
begin
  cases m₁ with g h₁ h₂,
  subst h₁, subst h₂,
  unfold transpose, congr' 1,
  rw grid_eq_iff_a_a, 
    {
      rw gen_aof_eq_gen,
      apply list.ext_le,
        {
          repeat { rw length_generate_eq_size },
          simp [size, relative_grid.rows, relative_grid.cols]
        },
        {
          intros n h₁ h₂,
          repeat { rw nth_generate },
          simp only [
            abs_data, (∘), relpoint_of_gpoint, prod_of_rel_point,
            function.uncurry, gtr, tr, relative_grid.data, grid.bl,
            relative_grid.rows, relative_grid.cols, tl, gtr, zero_add,
            agrid_of_fgrid_c, sub_zero
          ],
          simp,
          repeat { rw vector.nth_eq_nth_le },
          rw ← option.some_inj,
          repeat { rw ← list.nth_le_nth },
          repeat { rw ← coe_is_z_of_bounded },
          simp [z_of_bounded],
          repeat { rw ← coe_is_z_of_bounded },
          simp only [vector.to_list],
          simp only [z_of_bounded],
          conv { to_rhs, simp only [mul_comm] },
          rw nth_agrid_of_fgrid,
          rw nth_generate',
          simp [
            abs_data, relpoint_of_gpoint, prod_of_rel_point, grid.bl, tl,
            gtr, tr, grid.bl, function.uncurry, relative_grid.rows,
            relative_grid.cols, relative_grid.data
          ],
          unfold_coes, simp [z_of_bounded],
          rw vector.nth_eq_nth_le,
          rw list.nth_le_nth,
          apply congr_arg, congr' 1, simp,
          rw ← int.coe_nat_eq_coe_nat_iff,
          repeat { rw int.coe_nat_add },
          repeat { rw int.of_nat_eq_coe },
          repeat { rw int.coe_nat_mul },
          repeat { rw int.nat_abs_of_nonneg; try { apply int.coe_zero_le } },
          simp [int.mod_add_div],
          generalize eq₁ : (g.to_grid₀).c = c,
          generalize eq₂ : (g.to_grid₀).r = r,
          have H₁ : r > 0, from eq₂ ▸ (gt_and_gt_of_mul_gt g.h).1,
          have H₂ : r ≠ 0, {
            intros contra, rw contra at H₁, have : ¬0 > 0, from gt_irrefl _,
            contradiction
          },
          have H₃ : c > 0, from eq₁ ▸ (gt_and_gt_of_mul_gt g.h).2,
          rw length_generate_eq_size at h₁,
          simp [size, relative_grid.rows, relative_grid.cols] at h₁,
          repeat { rw ← int.coe_nat_div },
          repeat { rw ← int.coe_nat_mod },
          repeat { rw ← int.coe_nat_mul },
          repeat { rw ← int.coe_nat_add },
          repeat { rw ← int.coe_nat_div },
          repeat { rw ← int.coe_nat_add },
          rw int.coe_nat_eq_coe_nat_iff,
          rw mul_comm _ r,
          rw nat.add_mul_div_left,
          rw nat.div_div_eq_div_mul,
          rw @nat.div_eq_of_lt _ (c * r),
          simp,
          rw mul_comm,
          rw @nat.mod_eq_of_lt (n / c),
          apply nat.mod_add_div,
          rw nat.div_lt_iff_lt_mul,
          rw ← eq₁, rw ← eq₂, exact h₁,
          exact H₃,
          rw mul_comm,
          rw ← eq₁, rw ← eq₂, exact h₁,
          exact H₁,
          rw ← int.coe_nat_lt_coe_nat_iff,
          rw int.coe_nat_add,
          rw int.coe_nat_mul,
          repeat { rw int.nat_abs_of_nonneg },
          rw int.coe_nat_mod,
          rw int.coe_nat_div,
          rw int.mod_add_div,
          rw generate_eq_data at h₂,
          rw int.coe_nat_lt_coe_nat_iff,
          exact h₂,
          apply int.coe_zero_le,
          apply int.coe_zero_le,
          rw ← int.coe_nat_lt_coe_nat_iff,
          rw int.coe_nat_add,
          rw int.coe_nat_mul,
          repeat { rw int.nat_abs_of_nonneg; try { apply int.coe_zero_le } },
          rw length_generate_eq_size,
          unfold size relative_grid.rows relative_grid.cols,
          simp,
          rw add_comm,
          repeat { rw ← int.coe_nat_div },
          repeat { rw ← int.coe_nat_mod },
          repeat { rw ← int.coe_nat_mul },
          repeat { rw ← int.coe_nat_add },
          repeat { rw ← int.coe_nat_div },
          repeat { rw ← int.coe_nat_add },
          rw int.coe_nat_lt_coe_nat_iff,
          apply linearize_array,
          constructor,
          apply zero_le,
          rw nat.div_lt_iff_lt_mul,
          rw length_generate_eq_size at h₂,
          unfold size relative_grid.rows relative_grid.cols at h₂,
          exact h₂,
          have : (g.to_grid₀).c > 0, from (gt_and_gt_of_mul_gt g.h).2,
          exact this,
          constructor,
          apply zero_le,
          apply nat.mod_lt,
          have : (g.to_grid₀).c > 0, from (gt_and_gt_of_mul_gt g.h).2,
          exact this,
        }
    },
        {
          simp
        },
        {
          simp
        },
        {
          simp, cases g with g o, cases o, simp
        }
end

end operations

end matrix