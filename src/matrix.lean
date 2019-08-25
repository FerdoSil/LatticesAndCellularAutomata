import grid utils data.vector2 tactic.elide

open utils

namespace matrix

structure matrix (m n : ℕ) (α : Type) :=
  (g  : agrid₀ α)
  (hr : g.r = m)
  (hc : g.c = n)

section ext

variables {m n : ℕ} {α : Type} {m₁ m₂ : matrix m n α}

theorem ext_iff : m₁.g = m₂.g ↔ m₁ = m₂ :=
  by cases m₁; rcases m₂; simp

@[extensionality] theorem ext : m₁.g = m₂.g → m₁ = m₂ := ext_iff.1

end ext

section operations

variables {m n o p : ℕ} {α β γ δ : Type}

open relative_grid grid

lemma matrix_unempty {m₁ : matrix m n α} : m * n > 0 :=
  by rcases m₁ with ⟨⟨⟨_, _, _, _⟩, _⟩, _, _⟩; finish

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

instance [has_add α] : has_add (matrix m n α) := {
  add := λm₁ m₂,
    ⟨⟨⟨m, n, @matrix_unempty _ _ _ m₁,
      begin
        rcases m₁ with ⟨⟨⟨g₁r, g₁c, g₁h, g₁d⟩, g₁o⟩, hr₁, hc₁⟩,
        rcases m₂ with ⟨⟨⟨g₂r, g₂c, g₂h, g₂d⟩, g₂o⟩, hr₂, hc₂⟩,
        simp at hr₁ hc₁ hr₂ hc₂, substs hc₁ hr₁ hc₂ hr₂,
        exact vector.zip_with (+) g₁d g₂d
      end⟩, ⟨0, 0⟩⟩, rfl, rfl⟩
}

def transpose (m₁ : matrix m n α) : matrix n m α :=
  ⟨(agrid_of_fgrid ⟨
      n, m, begin
              cases m₁ with g h₁ h₂,
              subst h₁, subst h₂,
              exact mul_comm g.r g.c ▸ g.h
            end, ⟨m₁.g.o.y - m, m₁.g.o.x + n⟩,
      λx y, abs_data m₁.g ⟨
        ⟨y.1,
        begin
          cases y with y h, simp at h, simp [expand_gtr, grid.bl],
          have : ↑(relative_grid.rows (m₁.g)) = ↑m,
            by rcases m₁ with ⟨⟨⟨_, _, _, _⟩, _⟩, h₁, h₂⟩; substs h₁ h₂;
               simp [relative_grid.rows],
          rw this, exact h
        end⟩,
        ⟨x.1,
        begin
          cases x with x h, simp at h, simp [expand_gtr, grid.bl],
          have : ↑(relative_grid.cols (m₁.g)) = ↑n,
            by rcases m₁ with ⟨⟨⟨_, _, _, _⟩, _⟩, h₁, h₂⟩; substs h₁ h₂;
               simp [relative_grid.cols],
          rw this, exact h
        end⟩⟩⟩), by simp, by simp⟩

theorem transpose_transpose_id (m₁ : matrix m n α) :
  transpose (transpose m₁) = m₁ :=
begin
  cases m₁ with g h₁ h₂, subst h₁, subst h₂,
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
          intros n h₁ h₂, rw nth_le_generate_f, simp,
          simp [abs_data_eq_nth_a', tl, bl, vector.nth_eq_nth_le, vector.to_list],
          rw ← option.some_inj,
          rw [← list.nth_le_nth, nth_agrid_of_fgrid],
          have : |↑n % ↑g.to_grid₀.c| + g.to_grid₀.c * |↑n / ↑g.to_grid₀.c| <
                 list.length g.to_grid₀.data.val,
            by rw [mul_comm, mod_add_div_coe]; rw generate_eq_data at h₂; exact h₂,
          rw length_generate_eq_size at h₂, unfold size at h₂,
          generalize eq₁ : (g.to_grid₀).c = c,
          generalize eq₂ : (g.to_grid₀).r = r,
          have rpos : r > 0, from eq₂ ▸ (gt_and_gt_of_mul_gt g.h).1,
          have cpos : c > 0, from eq₁ ▸ (gt_and_gt_of_mul_gt g.h).2,
          have nltcr : n < c * r, by simp [rows, cols, mul_comm, *] at h₂; assumption,
          rw nth_generate_f,
          simp [abs_data_eq_nth_a', vector.nth_eq_nth_le, list.nth_le_nth this, vector.to_list],
          rw [← with_bot.some_eq_coe],
          simp [generate_eq_data],
          congr' 2,
            {
              simp [eq₁, eq₂],
              have rnezero : r ≠ 0, by intros contra; rw contra at rpos; linarith,
              rw ← int.coe_nat_eq_coe_nat_iff, simp,
              repeat { rw int.nat_abs_of_nonneg; try { apply int.coe_zero_le } },
              rw @int.add_mul_div_right _ _ r (by simpa),
              norm_cast, rw nat.div_div_eq_div_mul,
              simp[@nat.div_eq_of_lt n (c * r) nltcr],
              norm_cast, rw mul_comm at nltcr,
              have h₃ : ↑(n / c) < ↑r,
                by rwa [int.coe_nat_lt_coe_nat_iff, nat.div_lt_iff_lt_mul _ _ cpos],
              have h₄ : (0 : ℤ) ≤ ↑(n / c), by simp,
              rw @int.mod_eq_of_lt ↑(n / c) ↑r h₄ h₃, rw mul_comm,
              apply int.mod_add_div
            },
            {
              rw length_generate_eq_size, simp [size, cols, rows],
              rw [add_comm],
              apply linearize_array,
            }
          -- rw ← int.coe_nat_eq_coe_nat_iff,
          -- repeat { rw int.coe_nat_add },
          -- repeat { rw int.of_nat_eq_coe },
          -- repeat { rw int.coe_nat_mul },
          -- repeat { rw int.nat_abs_of_nonneg; try { apply int.coe_zero_le } },
          -- simp [int.mod_add_div],
          -- generalize eq₁ : (g.to_grid₀).c = c,
          -- generalize eq₂ : (g.to_grid₀).r = r,
          -- have H₁ : r > 0, from eq₂ ▸ (gt_and_gt_of_mul_gt g.h).1,
          -- have H₂ : r ≠ 0, {
          --   intros contra, rw contra at H₁, have : ¬0 > 0, from gt_irrefl _,
          --   contradiction
          -- },
          -- have H₃ : c > 0, from eq₁ ▸ (gt_and_gt_of_mul_gt g.h).2,
          -- rw length_generate_eq_size at h₁,
          -- simp [size, relative_grid.rows, relative_grid.cols] at h₁,
          -- repeat { rw ← int.coe_nat_div },
          -- repeat { rw ← int.coe_nat_mod },
          -- repeat { rw ← int.coe_nat_mul },
          -- repeat { rw ← int.coe_nat_add },
          -- repeat { rw ← int.coe_nat_div },
          -- repeat { rw ← int.coe_nat_add },
          -- rw int.coe_nat_eq_coe_nat_iff,
          -- rw mul_comm _ r,
          -- rw nat.add_mul_div_left,
          -- rw nat.div_div_eq_div_mul,
          -- rw @nat.div_eq_of_lt _ (c * r),
          -- simp,
          -- rw mul_comm,
          -- rw @nat.mod_eq_of_lt (n / c),
          -- apply nat.mod_add_div,
          -- rw nat.div_lt_iff_lt_mul,
          -- rw ← eq₁, rw ← eq₂, exact h₁,
          -- exact H₃,
          -- rw mul_comm,
          -- rw ← eq₁, rw ← eq₂, exact h₁,
          -- exact H₁,
          -- rw ← int.coe_nat_lt_coe_nat_iff,
          -- rw int.coe_nat_add,
          -- rw int.coe_nat_mul,
          -- repeat { rw int.nat_abs_of_nonneg; try { apply int.coe_zero_le } },
          -- rw length_generate_eq_size,
          -- unfold size relative_grid.rows relative_grid.cols,
          -- simp,
          -- rw add_comm,
          -- repeat { rw ← int.coe_nat_div },
          -- repeat { rw ← int.coe_nat_mod },
          -- repeat { rw ← int.coe_nat_mul },
          -- repeat { rw ← int.coe_nat_add },
          -- repeat { rw ← int.coe_nat_div },
          -- repeat { rw ← int.coe_nat_add },
          -- rw int.coe_nat_lt_coe_nat_iff,
          -- apply linearize_array,
          -- rw nat.div_lt_iff_lt_mul,
          -- rw length_generate_eq_size at h₂,
          -- unfold size relative_grid.rows relative_grid.cols at h₂,
          -- exact h₂,
          -- have : (g.to_grid₀).c > 0, from (gt_and_gt_of_mul_gt g.h).2,
          -- exact this,
          -- apply nat.mod_lt,
          -- have : (g.to_grid₀).c > 0, from (gt_and_gt_of_mul_gt g.h).2,
          -- exact this,
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